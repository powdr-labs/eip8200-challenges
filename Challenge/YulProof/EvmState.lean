import YulEvmCompiler.StateRel
import YulEvmCompiler.Optimizer.Implementation.MemorySpillStateSound

set_option warningAsError true

/-!
# Reusable EVM-dialect Yul state and memory helpers

Exact state transformers for common Yul builtins, plus pointwise frame
relations used to retain only the memory observations a source proof needs.
Nothing in this module depends on a challenge or cryptographic algorithm.
-/

namespace Challenge.YulProof.EvmState

open YulSemantics.EVM

def storeWordAt (st : EvmState) (p v : U256) : EvmState :=
  { touchMemory st p.toNat 32 with memory := storeWord st.memory p.toNat v }

def storeByteAt (st : EvmState) (p v : U256) : EvmState :=
  { touchMemory st p.toNat 1 with memory := storeByte st.memory p.toNat v }

/-- Two 32-byte Yul memory words do not overlap. -/
def WordDisjoint (p q : U256) : Prop :=
  p.toNat + 32 ≤ q.toNat ∨ q.toNat + 32 ≤ p.toNat

@[simp] theorem loadWord_storeWordAt (st : EvmState) (p v : U256) :
    loadWord (storeWordAt st p v).memory p.toNat = v := by
  exact YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord
    st.memory p.toNat v

theorem loadWord_storeWordAt_other (st : EvmState) (write read v : U256)
    (hdisjoint : WordDisjoint write read) :
    loadWord (storeWordAt st write v).memory read.toNat =
      loadWord st.memory read.toNat := by
  exact YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
    st.memory write.toNat read.toNat v hdisjoint

@[simp] theorem memory_storeByteAt_same (st : EvmState) (p v : U256) :
    (storeByteAt st p v).memory p.toNat = byteAt v 0 := by
  simp [storeByteAt, storeByte]

theorem memory_storeByteAt_other (st : EvmState) (p v : U256) (q : Nat)
    (hne : q ≠ p.toNat) :
    (storeByteAt st p v).memory q = st.memory q := by
  simp [storeByteAt, storeByte, hne]

theorem loadWord_storeByteAt_other (st : EvmState) (write read v : U256)
    (hdisjoint : write.toNat < read.toNat ∨ read.toNat + 32 ≤ write.toNat) :
    loadWord (storeByteAt st write v).memory read.toNat =
      loadWord st.memory read.toNat := by
  unfold loadWord
  apply List.foldl_ext _ _ 0
  intro _ i hi
  have hi32 : i < 32 := List.mem_range.mp hi
  rw [memory_storeByteAt_other]
  rcases hdisjoint with hbefore | hafter <;> omega

/-- The address of word `i` in a contiguous 32-byte word array. Arithmetic
is intentionally in `U256`, matching Yul's `add(base, mul(i, 32))`. -/
def wordOffset (base : U256) (i : Nat) : U256 :=
  base + BitVec.ofNat 256 i * 32

/-- State after clearing the first `count` words of a contiguous word array. -/
def clearWordsState (st : EvmState) (base : U256) : Nat → EvmState
  | 0 => st
  | count + 1 => storeWordAt (clearWordsState st base count) (wordOffset base count) 0

/-- One `mload` followed by one `mstore`, including both memory touches. -/
def copyWordAt (st : EvmState) (dst src : U256) : EvmState :=
  let loaded := touchMemory st src.toNat 32
  storeWordAt loaded dst (loadWord st.memory src.toNat)

/-- State after forward-copying the first `count` words between contiguous
word arrays. Reads observe prior writes, as in an ordinary Yul loop. -/
def copyWordsState (st : EvmState) (dst src : U256) : Nat → EvmState
  | 0 => st
  | count + 1 =>
      copyWordAt (copyWordsState st dst src count)
        (wordOffset dst count) (wordOffset src count)

@[simp] theorem clearWordsState_zero (st : EvmState) (base : U256) :
    clearWordsState st base 0 = st := rfl

@[simp] theorem clearWordsState_succ (st : EvmState) (base : U256) (count : Nat) :
    clearWordsState st base (count + 1) =
      storeWordAt (clearWordsState st base count) (wordOffset base count) 0 := rfl

@[simp] theorem copyWordsState_zero (st : EvmState) (dst src : U256) :
    copyWordsState st dst src 0 = st := rfl

@[simp] theorem copyWordsState_succ (st : EvmState) (dst src : U256) (count : Nat) :
    copyWordsState st dst src (count + 1) =
      copyWordAt (copyWordsState st dst src count)
        (wordOffset dst count) (wordOffset src count) := rfl

@[simp] theorem loadWord_copyWordAt (st : EvmState) (dst src : U256) :
    loadWord (copyWordAt st dst src).memory dst.toNat =
      loadWord st.memory src.toNat := by
  simp [copyWordAt]

def storeMany : EvmState → List (U256 × U256) → EvmState
  | st, [] => st
  | st, (p, v) :: rest => storeMany (storeWordAt st p v) rest

theorem loadWord_storeMany_preserved (st : EvmState)
    (stores : List (U256 × U256)) (p v : U256)
    (hload : loadWord st.memory p.toNat = v)
    (hall : ∀ q w, (q, w) ∈ stores →
      (q = p ∧ w = v) ∨ WordDisjoint q p) :
    loadWord (storeMany st stores).memory p.toNat = v := by
  induction stores generalizing st with
  | nil => exact hload
  | cons head rest ih =>
      rcases head with ⟨q, w⟩
      have hhead := hall q w (by simp)
      have hrest : ∀ q' w', (q', w') ∈ rest →
          (q' = p ∧ w' = v) ∨ WordDisjoint q' p := by
        intro q' w' hm
        exact hall q' w' (by simp [hm])
      simp only [storeMany]
      apply ih (st := storeWordAt st q w)
      · rcases hhead with hsame | hdisjoint
        · rw [hsame.1, hsame.2]
          exact YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord
            st.memory p.toNat v
        · unfold storeWordAt
          rw [YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
            st.memory q.toNat p.toNat w hdisjoint]
          exact hload
      · exact hrest

theorem loadWord_storeMany_member (st : EvmState)
    (stores : List (U256 × U256)) (p v : U256)
    (hmember : (p, v) ∈ stores)
    (hall : ∀ q w, (q, w) ∈ stores →
      (q = p ∧ w = v) ∨ WordDisjoint q p) :
    loadWord (storeMany st stores).memory p.toNat = v := by
  induction stores generalizing st with
  | nil => simp at hmember
  | cons head rest ih =>
      rcases head with ⟨q, w⟩
      have hrest : ∀ q' w', (q', w') ∈ rest →
          (q' = p ∧ w' = v) ∨ WordDisjoint q' p := by
        intro q' w' hm
        exact hall q' w' (by simp [hm])
      simp only [storeMany]
      simp only [List.mem_cons] at hmember
      rcases hmember with hsame | hmember
      · cases hsame
        apply loadWord_storeMany_preserved _ rest p v
        · exact YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord
            st.memory p.toNat v
        · exact hrest
      · exact ih (storeWordAt st q w) hmember hrest

def readLE32Value (memory : Nat → UInt8) (off : U256) : U256 :=
  let w := loadWord memory off.toNat
  let a := (w >>> 248) &&& 0xff
  let b := ((w >>> 240) &&& 0xff) <<< 8
  let c := ((w >>> 232) &&& 0xff) <<< 16
  let d := ((w >>> 224) &&& 0xff) <<< 24
  (a ||| b) ||| (c ||| d)

def mcopyState (st : EvmState) (dst src n : U256) : EvmState :=
  { touchMemory2 st dst.toNat n.toNat src.toNat n.toNat with
    memory := copyWithin st.memory dst.toNat src.toNat n.toNat }

theorem loadWord_copyWithin_window (memory : Nat → UInt8)
    (dst src n k : Nat) (hk : k + 32 ≤ n) :
    loadWord (copyWithin memory dst src n) (dst + k) =
      loadWord memory (src + k) := by
  unfold loadWord
  apply List.foldl_ext _ _ 0
  intro _ i hi
  have hi32 : i < 32 := List.mem_range.mp hi
  simp only [copyWithin]
  rw [if_pos (by omega)]
  have hoff : src + (dst + k + i - dst) = src + k + i := by omega
  rw [hoff]

theorem loadWord_copyWithin_other (memory : Nat → UInt8)
    (dst src n p : Nat) (hdisjoint : p + 32 ≤ dst ∨ dst + n ≤ p) :
    loadWord (copyWithin memory dst src n) p = loadWord memory p := by
  unfold loadWord
  apply List.foldl_ext _ _ 0
  intro _ i hi
  have hi32 : i < 32 := List.mem_range.mp hi
  simp only [copyWithin]
  rw [if_neg (by rcases hdisjoint with h | h <;> omega)]

theorem loadWord_mcopyState_other (st : EvmState) (dst src n : U256)
    (p : Nat) (hdisjoint : p + 32 ≤ dst.toNat ∨ dst.toNat + n.toNat ≤ p) :
    loadWord (mcopyState st dst src n).memory p = loadWord st.memory p := by
  unfold mcopyState
  exact loadWord_copyWithin_other st.memory dst.toNat src.toNat n.toNat p hdisjoint

/-- Pointwise agreement from `cutoff` upward. -/
def MemoryEqFrom (cutoff : Nat) (before after : EvmState) : Prop :=
  ∀ p, cutoff ≤ p → after.memory p = before.memory p

namespace MemoryEqFrom

theorem refl (cutoff : Nat) (st : EvmState) : MemoryEqFrom cutoff st st := by
  intro _ _
  rfl

theorem trans {cutoff : Nat} {a b c : EvmState}
    (hab : MemoryEqFrom cutoff a b) (hbc : MemoryEqFrom cutoff b c) :
    MemoryEqFrom cutoff a c := by
  intro p hp
  rw [hbc p hp, hab p hp]

theorem loadWord {cutoff : Nat} {before after : EvmState}
    (h : MemoryEqFrom cutoff before after) (p : Nat) (hp : cutoff ≤ p) :
    YulSemantics.EVM.loadWord after.memory p =
      YulSemantics.EVM.loadWord before.memory p := by
  unfold YulSemantics.EVM.loadWord
  apply List.foldl_ext _ _ 0
  intro _ i hi
  have hi' : i < 32 := List.mem_range.mp hi
  rw [h (p + i) (by omega)]

theorem readBytes {cutoff : Nat} {before after : EvmState}
    (h : MemoryEqFrom cutoff before after) (p n : Nat) (hp : cutoff ≤ p) :
    YulSemantics.EVM.readBytes after.memory p n =
      YulSemantics.EVM.readBytes before.memory p n := by
  unfold YulSemantics.EVM.readBytes
  apply List.map_congr_left
  intro i hi
  rw [h (p + i) (by omega)]

theorem storeWordAt {cutoff : Nat} {before after : EvmState}
    (h : MemoryEqFrom cutoff before after) (p v : U256)
    (hp : p.toNat + 32 ≤ cutoff) :
    MemoryEqFrom cutoff before (storeWordAt after p v) := by
  intro q hq
  unfold Challenge.YulProof.EvmState.storeWordAt
  simp only [storeWord]
  split
  · rename_i hwindow
    omega
  · exact h q hq

theorem storeByteAt {cutoff : Nat} {before after : EvmState}
    (h : MemoryEqFrom cutoff before after) (p v : U256)
    (hp : p.toNat < cutoff) :
    MemoryEqFrom cutoff before
      (Challenge.YulProof.EvmState.storeByteAt after p v) := by
  intro q hq
  unfold Challenge.YulProof.EvmState.storeByteAt
  simp only [storeByte]
  rw [if_neg (by omega)]
  exact h q hq

theorem touch (cutoff : Nat) (st : EvmState) (offset size : Nat) :
    MemoryEqFrom cutoff st (touchMemory st offset size) := by
  intro _ _
  rfl

theorem copyWordAt {cutoff : Nat} {before after : EvmState}
    (h : MemoryEqFrom cutoff before after) (dst src : U256)
    (hdst : dst.toNat + 32 ≤ cutoff) :
    MemoryEqFrom cutoff before
      (Challenge.YulProof.EvmState.copyWordAt after dst src) := by
  unfold Challenge.YulProof.EvmState.copyWordAt
  apply storeWordAt
  · exact trans h (touch cutoff after src.toNat 32)
  · exact hdst

theorem storeMany (st : EvmState) (stores : List (U256 × U256))
    (cutoff : Nat) (hall : ∀ p v, (p, v) ∈ stores → p.toNat + 32 ≤ cutoff) :
    MemoryEqFrom cutoff st (Challenge.YulProof.EvmState.storeMany st stores) := by
  induction stores generalizing st with
  | nil => exact refl cutoff st
  | cons head rest ih =>
      rcases head with ⟨p, v⟩
      rw [Challenge.YulProof.EvmState.storeMany]
      exact trans (storeWordAt (refl cutoff st) p v (hall p v (by simp)))
        (ih (Challenge.YulProof.EvmState.storeWordAt st p v)
          (fun p' v' hm => hall p' v' (by simp [hm])))

theorem clearWordsState {cutoff : Nat} {before after : EvmState}
    (h : MemoryEqFrom cutoff before after) (base : U256) (count : Nat)
    (hall : ∀ i, i < count → (wordOffset base i).toNat + 32 ≤ cutoff) :
    MemoryEqFrom cutoff before
      (Challenge.YulProof.EvmState.clearWordsState after base count) := by
  induction count with
  | zero => simpa
  | succ count ih =>
      rw [Challenge.YulProof.EvmState.clearWordsState_succ]
      apply storeWordAt
      · exact ih (fun i hi => hall i (by omega))
      · exact hall count (by omega)

theorem copyWordsState {cutoff : Nat} {before after : EvmState}
    (h : MemoryEqFrom cutoff before after) (dst src : U256) (count : Nat)
    (hall : ∀ i, i < count → (wordOffset dst i).toNat + 32 ≤ cutoff) :
    MemoryEqFrom cutoff before
      (Challenge.YulProof.EvmState.copyWordsState after dst src count) := by
  induction count with
  | zero => simpa
  | succ count ih =>
      rw [Challenge.YulProof.EvmState.copyWordsState_succ]
      apply copyWordAt
      · exact ih (fun i hi => hall i (by omega))
      · exact hall count (by omega)

theorem mcopyState (cutoff : Nat) (st : EvmState) (dst src n : U256)
    (hdst : dst.toNat + n.toNat ≤ cutoff) :
    MemoryEqFrom cutoff st (Challenge.YulProof.EvmState.mcopyState st dst src n) := by
  intro p hp
  unfold Challenge.YulProof.EvmState.mcopyState copyWithin
  simp only
  rw [if_neg (by omega)]

end MemoryEqFrom

/-- Pointwise agreement strictly below `cutoff`. -/
def MemoryEqBefore (cutoff : Nat) (before after : EvmState) : Prop :=
  ∀ p, p < cutoff → after.memory p = before.memory p

namespace MemoryEqBefore

theorem refl (cutoff : Nat) (st : EvmState) : MemoryEqBefore cutoff st st := by
  intro _ _
  rfl

theorem trans {cutoff : Nat} {a b c : EvmState}
    (hab : MemoryEqBefore cutoff a b) (hbc : MemoryEqBefore cutoff b c) :
    MemoryEqBefore cutoff a c := by
  intro p hp
  rw [hbc p hp, hab p hp]

theorem loadWord {cutoff : Nat} {before after : EvmState}
    (h : MemoryEqBefore cutoff before after) (p : Nat) (hp : p + 32 ≤ cutoff) :
    YulSemantics.EVM.loadWord after.memory p =
      YulSemantics.EVM.loadWord before.memory p := by
  unfold YulSemantics.EVM.loadWord
  apply List.foldl_ext _ _ 0
  intro _ i hi
  have hi' : i < 32 := List.mem_range.mp hi
  rw [h (p + i) (by omega)]

theorem readBytes {cutoff : Nat} {before after : EvmState}
    (h : MemoryEqBefore cutoff before after) (p n : Nat)
    (hp : p + n ≤ cutoff) :
    YulSemantics.EVM.readBytes after.memory p n =
      YulSemantics.EVM.readBytes before.memory p n := by
  unfold YulSemantics.EVM.readBytes
  apply List.map_congr_left
  intro i hi
  have hi' : i < n := List.mem_range.mp hi
  rw [h (p + i) (by omega)]

theorem storeWordAt {cutoff : Nat} {before after : EvmState}
    (h : MemoryEqBefore cutoff before after) (p v : U256)
    (hp : cutoff ≤ p.toNat) :
    MemoryEqBefore cutoff before (storeWordAt after p v) := by
  intro q hq
  unfold Challenge.YulProof.EvmState.storeWordAt
  simp only [storeWord]
  split
  · rename_i hwindow
    omega
  · exact h q hq

theorem storeByteAt {cutoff : Nat} {before after : EvmState}
    (h : MemoryEqBefore cutoff before after) (p v : U256)
    (hp : cutoff ≤ p.toNat) :
    MemoryEqBefore cutoff before
      (Challenge.YulProof.EvmState.storeByteAt after p v) := by
  intro q hq
  unfold Challenge.YulProof.EvmState.storeByteAt
  simp only [storeByte]
  rw [if_neg (by omega)]
  exact h q hq

theorem touch (cutoff : Nat) (st : EvmState) (offset size : Nat) :
    MemoryEqBefore cutoff st (touchMemory st offset size) := by
  intro _ _
  rfl

theorem copyWordAt {cutoff : Nat} {before after : EvmState}
    (h : MemoryEqBefore cutoff before after) (dst src : U256)
    (hdst : cutoff ≤ dst.toNat) :
    MemoryEqBefore cutoff before
      (Challenge.YulProof.EvmState.copyWordAt after dst src) := by
  unfold Challenge.YulProof.EvmState.copyWordAt
  apply storeWordAt
  · exact trans h (touch cutoff after src.toNat 32)
  · exact hdst

theorem clearWordsState {cutoff : Nat} {before after : EvmState}
    (h : MemoryEqBefore cutoff before after) (base : U256) (count : Nat)
    (hall : ∀ i, i < count → cutoff ≤ (wordOffset base i).toNat) :
    MemoryEqBefore cutoff before
      (Challenge.YulProof.EvmState.clearWordsState after base count) := by
  induction count with
  | zero => simpa
  | succ count ih =>
      rw [Challenge.YulProof.EvmState.clearWordsState_succ]
      apply storeWordAt
      · exact ih (fun i hi => hall i (by omega))
      · exact hall count (by omega)

theorem copyWordsState {cutoff : Nat} {before after : EvmState}
    (h : MemoryEqBefore cutoff before after) (dst src : U256) (count : Nat)
    (hall : ∀ i, i < count → cutoff ≤ (wordOffset dst i).toNat) :
    MemoryEqBefore cutoff before
      (Challenge.YulProof.EvmState.copyWordsState after dst src count) := by
  induction count with
  | zero => simpa
  | succ count ih =>
      rw [Challenge.YulProof.EvmState.copyWordsState_succ]
      apply copyWordAt
      · exact ih (fun i hi => hall i (by omega))
      · exact hall count (by omega)

end MemoryEqBefore

end Challenge.YulProof.EvmState
