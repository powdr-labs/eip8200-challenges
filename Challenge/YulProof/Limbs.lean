import Challenge.YulProof.EvmState
import Mathlib.Data.Nat.Digits.Lemmas

set_option warningAsError true

/-!
# Reusable limb arrays in Yul memory

This module gives contiguous little-endian 256-bit words in the Yul EVM
memory model a challenge-independent mathematical interface.  It also proves
the framing facts needed for the shared clear and forward-copy state
transformers from `Challenge.YulProof.EvmState`.
-/

namespace Challenge.YulProof.Limbs

open YulSemantics.EVM
open Challenge.YulProof.EvmState

/-- Radix of one EVM memory word. -/
def radix : Nat := 2 ^ 256

/-- Fixed-width little-endian radix expansion. -/
def limbDigits (count value : Nat) : List Nat :=
  Nat.digitsAppend radix count value

/-- Consecutive little-endian Yul words, viewed as natural-number limbs. -/
def memoryLimbs (memory : Nat → UInt8) (ptr count : Nat) : List Nat :=
  (List.range count).map fun i => (loadWord memory (ptr + 32 * i)).toNat

/-- `count` words at `ptr` are the fixed-width limb encoding of `value`. -/
def Represents (memory : Nat → UInt8) (ptr count value : Nat) : Prop :=
  value < radix ^ count ∧
    memoryLimbs memory ptr count = limbDigits count value

theorem radix_gt_one : 1 < radix := by
  norm_num [radix]

theorem radix_pos : 0 < radix := Nat.zero_lt_of_lt radix_gt_one

@[simp] theorem length_limbDigits {count value : Nat}
    (hvalue : value < radix ^ count) :
    (limbDigits count value).length = count := by
  exact Nat.length_digitsAppend radix_gt_one count hvalue

theorem limbDigits_lt {count value digit : Nat}
    (hdigit : digit ∈ limbDigits count value) : digit < radix := by
  exact Nat.lt_of_mem_digitsAppend radix_gt_one count digit hdigit

theorem value_limbDigits (count value : Nat) :
    Nat.ofDigits radix (limbDigits count value) = value := by
  rw [limbDigits, Nat.digitsAppend, Nat.ofDigits_append_replicate_zero,
    Nat.ofDigits_digits]

@[simp] theorem length_memoryLimbs (memory : Nat → UInt8)
    (ptr count : Nat) :
    (memoryLimbs memory ptr count).length = count := by
  simp [memoryLimbs]

theorem memoryLimb_lt (memory : Nat → UInt8) (ptr count : Nat)
    {digit : Nat} (hdigit : digit ∈ memoryLimbs memory ptr count) :
    digit < radix := by
  simp only [memoryLimbs, List.mem_map] at hdigit
  rcases hdigit with ⟨i, _, rfl⟩
  exact (loadWord memory (ptr + 32 * i)).isLt

theorem value_of_represents {memory : Nat → UInt8} {ptr count value : Nat}
    (hrep : Represents memory ptr count value) :
    Nat.ofDigits radix (memoryLimbs memory ptr count) = value := by
  rw [hrep.2, value_limbDigits]

theorem represents_value_unique {memory : Nat → UInt8}
    {ptr count left right : Nat}
    (hleft : Represents memory ptr count left)
    (hright : Represents memory ptr count right) : left = right := by
  rw [← value_of_represents hleft, ← value_of_represents hright]

theorem represents_iff_value {memory : Nat → UInt8} {ptr count value : Nat}
    (hvalue : value < radix ^ count) :
    Represents memory ptr count value ↔
      Nat.ofDigits radix (memoryLimbs memory ptr count) = value := by
  constructor
  · exact value_of_represents
  · intro heq
    refine ⟨hvalue, ?_⟩
    apply Nat.ofDigits_inj_of_len_eq radix_gt_one
    · rw [length_memoryLimbs, length_limbDigits hvalue]
    · exact fun digit hdigit => memoryLimb_lt _ _ _ hdigit
    · exact fun digit hdigit => limbDigits_lt hdigit
    · rw [heq, value_limbDigits]

theorem wordOffset_ofNat (base i : Nat)
    (hfit : base + 32 * i < 2 ^ 256) :
    (wordOffset (BitVec.ofNat 256 base) i).toNat = base + 32 * i := by
  simp [wordOffset, BitVec.toNat_add, BitVec.toNat_mul, Nat.mul_comm i 32]
  simpa using hfit

theorem memoryLimbs_succ (memory : Nat → UInt8) (ptr count : Nat) :
    memoryLimbs memory ptr (count + 1) =
      memoryLimbs memory ptr count ++
        [(loadWord memory (ptr + 32 * count)).toNat] := by
  simp [memoryLimbs, List.range_succ]

theorem memoryLimbs_store_next (st : EvmState) (ptr count : Nat) (v : U256)
    (hfit : ptr + 32 * count < 2 ^ 256) :
    memoryLimbs
        (storeWordAt st (wordOffset (BitVec.ofNat 256 ptr) count) v).memory
        ptr (count + 1) = memoryLimbs st.memory ptr count ++ [v.toNat] := by
  rw [memoryLimbs_succ]
  have hprefix :
      memoryLimbs
          (storeWordAt st (wordOffset (BitVec.ofNat 256 ptr) count) v).memory
          ptr count = memoryLimbs st.memory ptr count := by
    unfold memoryLimbs
    apply List.map_congr_left
    intro i hi
    have hi' : i < count := by simpa using hi
    change BitVec.toNat
        (loadWord (storeWord st.memory
          (wordOffset (BitVec.ofNat 256 ptr) count).toNat v)
          (ptr + 32 * i)) = _
    rw [YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
    right
    rw [wordOffset_ofNat ptr count hfit]
    omega
  have hlast :
      loadWord
          (storeWordAt st (wordOffset (BitVec.ofNat 256 ptr) count) v).memory
          (ptr + 32 * count) = v := by
    rw [← wordOffset_ofNat ptr count hfit]
    exact loadWord_storeWordAt st _ v
  rw [hprefix, hlast]

theorem memoryLimbs_store_disjoint (st : EvmState) (write : U256)
    (ptr count : Nat) (v : U256)
    (hdisjoint : write.toNat + 32 ≤ ptr ∨ ptr + 32 * count ≤ write.toNat) :
    memoryLimbs (storeWordAt st write v).memory ptr count =
      memoryLimbs st.memory ptr count := by
  unfold memoryLimbs
  apply List.map_congr_left
  intro i hi
  have hi' : i < count := by simpa using hi
  change BitVec.toNat
      (loadWord (storeWord st.memory write.toNat v) (ptr + 32 * i)) = _
  rw [YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
  rcases hdisjoint with hbefore | hafter
  · left; omega
  · right; omega

theorem memoryLimbs_clearWordsState (st : EvmState) (ptr count : Nat)
    (hfit : ptr + 32 * count < 2 ^ 256) :
    memoryLimbs (clearWordsState st (BitVec.ofNat 256 ptr) count).memory
      ptr count = List.replicate count 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [clearWordsState_succ,
        memoryLimbs_store_next _ _ _ _ (by omega), ih (by omega)]
      simp [List.replicate_succ']

theorem clearWordsState_represents_zero (st : EvmState) (ptr count : Nat)
    (hfit : ptr + 32 * count < 2 ^ 256) :
    Represents (clearWordsState st (BitVec.ofNat 256 ptr) count).memory
      ptr count 0 := by
  refine ⟨Nat.pow_pos radix_pos, ?_⟩
  rw [memoryLimbs_clearWordsState st ptr count hfit]
  simp [limbDigits, Nat.digitsAppend]

theorem memoryLimbs_clearWordsState_disjoint (st : EvmState)
    (dst ptr total count : Nat) (hcount : count ≤ total)
    (hdstfit : dst + 32 * total < 2 ^ 256)
    (hdisjoint : dst + 32 * total ≤ ptr ∨ ptr + 32 * total ≤ dst) :
    memoryLimbs (clearWordsState st (BitVec.ofNat 256 dst) count).memory
      ptr total = memoryLimbs st.memory ptr total := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [clearWordsState_succ, memoryLimbs_store_disjoint]
      · exact ih (by omega)
      · rw [wordOffset_ofNat dst count (by omega)]
        rcases hdisjoint with hbefore | hafter
        · left; omega
        · right; omega

theorem clearWordsState_preserves (st : EvmState) (dst ptr count value : Nat)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ dst)
    (hrep : Represents st.memory ptr count value) :
    Represents (clearWordsState st (BitVec.ofNat 256 dst) count).memory
      ptr count value :=
  ⟨hrep.1, (memoryLimbs_clearWordsState_disjoint st dst ptr count count
    (by omega) hdstfit hdisjoint).trans hrep.2⟩

theorem loadWord_copyWordsState_source (st : EvmState)
    (dst src total count j : Nat) (hcount : count ≤ j) (hj : j < total)
    (hdstfit : dst + 32 * total < 2 ^ 256)
    (hdisjoint : dst + 32 * total ≤ src ∨ src + 32 * total ≤ dst) :
    loadWord (copyWordsState st (BitVec.ofNat 256 dst)
      (BitVec.ofNat 256 src) count).memory (src + 32 * j) =
      loadWord st.memory (src + 32 * j) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [copyWordsState_succ]
      simp only [copyWordAt, storeWordAt]
      rw [YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
      · exact ih (by omega)
      · rw [wordOffset_ofNat dst count (by omega)]
        rcases hdisjoint with hbefore | hafter
        · left; omega
        · right; omega

theorem memoryLimbs_copyWordsState (st : EvmState) (dst src count : Nat)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hsrcfit : src + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ src ∨ src + 32 * count ≤ dst) :
    memoryLimbs (copyWordsState st (BitVec.ofNat 256 dst)
      (BitVec.ofNat 256 src) count).memory dst count =
      memoryLimbs st.memory src count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [copyWordsState_succ]
      let before := copyWordsState st (BitVec.ofNat 256 dst)
        (BitVec.ofNat 256 src) count
      have hsrcAddr := wordOffset_ofNat src count (by omega)
      have hsrcWord : loadWord before.memory (src + 32 * count) =
          loadWord st.memory (src + 32 * count) :=
        loadWord_copyWordsState_source st dst src (count + 1) count count
          (by omega) (by omega) (by omega) hdisjoint
      rw [copyWordAt, hsrcAddr]
      rw [memoryLimbs_store_next _ _ _ _ (by omega),
        show (touchMemory before (src + 32 * count) 32).memory = before.memory by rfl,
        ih (by omega) (by omega) (by rcases hdisjoint with h | h <;> omega),
        hsrcWord, memoryLimbs_succ]

theorem copyWordsState_represents (st : EvmState) (dst src count value : Nat)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hsrcfit : src + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ src ∨ src + 32 * count ≤ dst)
    (hrep : Represents st.memory src count value) :
    Represents (copyWordsState st (BitVec.ofNat 256 dst)
      (BitVec.ofNat 256 src) count).memory dst count value :=
  ⟨hrep.1, (memoryLimbs_copyWordsState st dst src count hdstfit hsrcfit
    hdisjoint).trans hrep.2⟩

theorem memoryLimbs_copyWordsState_disjoint (st : EvmState)
    (dst src ptr total count : Nat) (hcount : count ≤ total)
    (hdstfit : dst + 32 * total < 2 ^ 256)
    (hdisjoint : dst + 32 * total ≤ ptr ∨ ptr + 32 * total ≤ dst) :
    memoryLimbs (copyWordsState st (BitVec.ofNat 256 dst)
      (BitVec.ofNat 256 src) count).memory ptr total =
      memoryLimbs st.memory ptr total := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [copyWordsState_succ]
      simp only [copyWordAt]
      rw [memoryLimbs_store_disjoint]
      · simpa [YulSemantics.EVM.touchMemory] using ih (by omega)
      · rw [wordOffset_ofNat dst count (by omega)]
        rcases hdisjoint with hbefore | hafter
        · left; omega
        · right; omega

theorem copyWordsState_preserves (st : EvmState)
    (dst src ptr count value : Nat)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ dst)
    (hrep : Represents st.memory ptr count value) :
    Represents (copyWordsState st (BitVec.ofNat 256 dst)
      (BitVec.ofNat 256 src) count).memory ptr count value :=
  ⟨hrep.1, (memoryLimbs_copyWordsState_disjoint st dst src ptr count count
    (by omega) hdstfit hdisjoint).trans hrep.2⟩

end Challenge.YulProof.Limbs
