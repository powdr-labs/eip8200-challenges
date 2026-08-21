import Challenge.Modexp.Reference.Proofs.Yul.BigMul
import Challenge.Modexp.Reference.Proofs.Limbs

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-!
# Mathematical interpretation of the direct Yul big-number states

The Yul interpreter models memory as a total byte function, whereas the
bytecode development's `Limbs.Represents` uses the machine's finite
`ByteArray`.  `Represents` below is the corresponding predicate for source
states.  It deliberately reuses the canonical digits and all arithmetic
lemmas from `Proofs.Limbs`; only the memory observation is source-specific.
-/

namespace Challenge.Modexp.Reference.Proofs.Yul.BigMath

open YulSemantics.EVM
open Challenge.YulProof.EvmState

/-- Consecutive little-endian Yul words, viewed as natural-number limbs. -/
def memoryLimbs (memory : Nat → UInt8) (ptr count : Nat) : List Nat :=
  (List.range count).map fun i => (loadWord memory (ptr + 32 * i)).toNat

/-- A mathematical integer represented by little-endian words in a direct
source-Yul state. -/
def Represents (memory : Nat → UInt8) (ptr count value : Nat) : Prop :=
  value < Limbs.radix ^ count ∧
    memoryLimbs memory ptr count = Limbs.limbDigits count value

@[simp] theorem length_memoryLimbs (memory : Nat → UInt8) (ptr count : Nat) :
    (memoryLimbs memory ptr count).length = count := by
  simp [memoryLimbs]

theorem memoryLimb_lt (memory : Nat → UInt8) (ptr count : Nat)
    {digit : Nat} (hdigit : digit ∈ memoryLimbs memory ptr count) :
    digit < Limbs.radix := by
  simp only [memoryLimbs, List.mem_map] at hdigit
  rcases hdigit with ⟨i, _, rfl⟩
  exact (loadWord memory (ptr + 32 * i)).isLt

theorem value_of_represents {memory : Nat → UInt8} {ptr count value : Nat}
    (hrep : Represents memory ptr count value) :
    Nat.ofDigits Limbs.radix (memoryLimbs memory ptr count) = value := by
  rw [hrep.2, Limbs.value_limbDigits]

theorem represents_iff_value {memory : Nat → UInt8} {ptr count value : Nat}
    (hvalue : value < Limbs.radix ^ count) :
    Represents memory ptr count value ↔
      Nat.ofDigits Limbs.radix (memoryLimbs memory ptr count) = value := by
  constructor
  · exact value_of_represents
  · intro heq
    refine ⟨hvalue, ?_⟩
    apply Nat.ofDigits_inj_of_len_eq Limbs.radix_gt_one
    · rw [length_memoryLimbs, Limbs.length_limbDigits hvalue]
    · exact fun digit hdigit => memoryLimb_lt _ _ _ hdigit
    · exact fun digit hdigit => Limbs.limbDigits_lt hdigit
    · rw [heq, Limbs.value_limbDigits]

theorem limbAddr_ofNat (base i : Nat) (hfit : base + 32 * i < 2 ^ 256) :
    (BigArithmetic.limbAddr (BitVec.ofNat 256 base) i).toNat =
      base + 32 * i := by
  simp [BigArithmetic.limbAddr, BitVec.toNat_add, BitVec.toNat_mul,
    Nat.mul_comm i 32]
  simpa using hfit

theorem memoryLimbs_succ (memory : Nat → UInt8) (ptr count : Nat) :
    memoryLimbs memory ptr (count + 1) =
      memoryLimbs memory ptr count ++
        [(loadWord memory (ptr + 32 * count)).toNat] := by
  simp [memoryLimbs, List.range_succ]

theorem memoryLimbs_store_next (st : EvmState) (ptr count : Nat) (v : U256)
    (hfit : ptr + 32 * count < 2 ^ 256) :
    memoryLimbs
        (storeWordAt st
          (BigArithmetic.limbAddr (BitVec.ofNat 256 ptr) count) v).memory
        ptr (count + 1) = memoryLimbs st.memory ptr count ++ [v.toNat] := by
  rw [memoryLimbs_succ]
  have hprefix :
      memoryLimbs
          (storeWordAt st
            (BigArithmetic.limbAddr (BitVec.ofNat 256 ptr) count) v).memory
          ptr count = memoryLimbs st.memory ptr count := by
    unfold memoryLimbs
    apply List.map_congr_left
    intro i hi
    have hi' : i < count := by simpa using hi
    change BitVec.toNat
        (loadWord (storeWord st.memory
          (BigArithmetic.limbAddr (BitVec.ofNat 256 ptr) count).toNat v)
          (ptr + 32 * i)) = _
    rw [YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
    right
    rw [limbAddr_ofNat ptr count hfit]
    omega
  have hlast :
      loadWord
          (storeWordAt st
            (BigArithmetic.limbAddr (BitVec.ofNat 256 ptr) count) v).memory
          (ptr + 32 * count) = v := by
    rw [← limbAddr_ofNat ptr count hfit]
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

/-! ## Addition phase -/

theorem carryWord_toNat (smaller larger : U256) :
    (BigArithmetic.carryWord smaller larger).toNat =
      if smaller.toNat < larger.toNat then 1 else 0 := by
  by_cases h : smaller.toNat < larger.toNat
  · simp [BigArithmetic.carryWord, YulSemantics.EVM.b2w, BitVec.ult, h]
  · simp [BigArithmetic.carryWord, YulSemantics.EVM.b2w, BitVec.ult, h]

theorem mask_toNat (word : U256) {take : Nat} (htake : take ≤ 1) :
    (word &&& (0 - BitVec.ofNat 256 take)).toNat = take * word.toNat := by
  interval_cases take
  · simp
  · simp only [Nat.one_mul]
    apply congrArg BitVec.toNat
    bv_decide

theorem loadWord_addPhase_future (st : EvmState) (dst src mask : U256)
    (ptr count j : Nat) (hptr : dst = BitVec.ofNat 256 ptr)
    (hcount : count ≤ j) (hfit : ptr + 32 * j < 2 ^ 256) :
    loadWord (BigArithmetic.addPhase st dst src mask count).state.memory
        (ptr + 32 * j) = loadWord st.memory (ptr + 32 * j) := by
  subst dst
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [BigArithmetic.addPhase]
      simp only [BigArithmetic.addStep, storeWordAt]
      rw [YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
      · exact ih (by omega)
      · left
        rw [limbAddr_ofNat ptr count (by omega)]
        omega

theorem loadWord_addPhase_source (st : EvmState) (dst src mask : U256)
    (dstPtr srcPtr total count j : Nat)
    (hdst : dst = BitVec.ofNat 256 dstPtr)
    (hsrc : src = BitVec.ofNat 256 srcPtr) (hcount : count ≤ j)
    (hj : j < total) (hdstfit : dstPtr + 32 * total < 2 ^ 256)
    (hsrcfit : srcPtr + 32 * total < 2 ^ 256)
    (halias : dstPtr = srcPtr ∨ dstPtr + 32 * total ≤ srcPtr ∨
      srcPtr + 32 * total ≤ dstPtr) :
    loadWord (BigArithmetic.addPhase st dst src mask count).state.memory
        (srcPtr + 32 * j) = loadWord st.memory (srcPtr + 32 * j) := by
  rw [hdst, hsrc]
  rcases halias with hsame | hdisjoint
  · subst srcPtr
    exact loadWord_addPhase_future st _ _ mask dstPtr count j rfl hcount
      (by omega)
  · induction count with
    | zero => rfl
    | succ count ih =>
        rw [BigArithmetic.addPhase]
        simp only [BigArithmetic.addStep, storeWordAt]
        rw [YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
        · exact ih (by omega)
        · rw [limbAddr_ofNat dstPtr count (by omega)]
          rcases hdisjoint with hbefore | hafter
          · left; omega
          · right; omega

structure AddNatPhase where
  digits : List Nat
  carry : Nat

def addNatPhase (memory : Nat → UInt8) (dst src take : Nat) :
    Nat → AddNatPhase
  | 0 => ⟨[], 0⟩
  | i + 1 =>
      let before := addNatPhase memory dst src take i
      let x := (loadWord memory (dst + 32 * i)).toNat
      let y := (loadWord memory (src + 32 * i)).toNat
      let total := x + take * y + before.carry
      ⟨before.digits ++ [total % Limbs.radix], total / Limbs.radix⟩

theorem addNatPhase_eq_addDigitLists (memory : Nat → UInt8)
    (dst src take count : Nat) :
    let natural := addNatPhase memory dst src take count
    let result := Limbs.addDigitLists (memoryLimbs memory dst count)
      ((memoryLimbs memory src count).map (take * ·)) 0
    natural.digits = result.1 ∧ natural.carry = result.2 := by
  induction count with
  | zero => simp [addNatPhase, memoryLimbs, Limbs.addDigitLists]
  | succ count ih =>
      rw [addNatPhase, memoryLimbs_succ, memoryLimbs_succ,
        List.map_append, List.map_singleton]
      rw [Limbs.addDigitLists_append_single (by simp)]
      rcases ih with ⟨hdigits, hcarry⟩
      simp only
      rw [hdigits, hcarry]
      exact ⟨rfl, rfl⟩

theorem addPhase_matches_nat (st : EvmState)
    (dstPtr srcPtr total count take : Nat) (hcount : count ≤ total)
    (htake : take ≤ 1) (hdstfit : dstPtr + 32 * total < 2 ^ 256)
    (hsrcfit : srcPtr + 32 * total < 2 ^ 256)
    (halias : dstPtr = srcPtr ∨ dstPtr + 32 * total ≤ srcPtr ∨
      srcPtr + 32 * total ≤ dstPtr) :
    let phase := BigArithmetic.addPhase st (BitVec.ofNat 256 dstPtr)
      (BitVec.ofNat 256 srcPtr) (0 - BitVec.ofNat 256 take) count
    let natural := addNatPhase st.memory dstPtr srcPtr take count
    memoryLimbs phase.state.memory dstPtr count = natural.digits ∧
      phase.carry.toNat = natural.carry ∧ natural.carry ≤ 1 := by
  induction count with
  | zero =>
      simp [BigArithmetic.addPhase, addNatPhase, memoryLimbs]
  | succ count ih =>
      have hi : count < total := by omega
      have hbefore := ih (by omega)
      let before := BigArithmetic.addPhase st (BitVec.ofNat 256 dstPtr)
        (BitVec.ofNat 256 srcPtr) (0 - BitVec.ofNat 256 take) count
      let naturalBefore := addNatPhase st.memory dstPtr srcPtr take count
      let x := loadWord before.state.memory (dstPtr + 32 * count)
      let source := loadWord before.state.memory (srcPtr + 32 * count)
      let y := source &&& (0 - BitVec.ofNat 256 take)
      have hx : x = loadWord st.memory (dstPtr + 32 * count) :=
        loadWord_addPhase_future st _ _ _ dstPtr count count rfl (by omega)
          (by omega)
      have hsource : source = loadWord st.memory (srcPtr + 32 * count) :=
        loadWord_addPhase_source st _ _ _ dstPtr srcPtr total count count rfl rfl
          (by omega) hi hdstfit hsrcfit halias
      have hy : y.toNat = take * (loadWord st.memory
          (srcPtr + 32 * count)).toNat := by
        rw [show y = source &&& (0 - BitVec.ofNat 256 take) by rfl,
          mask_toNat source htake, hsource]
      have hcarryLe : naturalBefore.carry ≤ 1 := hbefore.2.2
      have hbeforeCarry : before.carry.toNat = naturalBefore.carry :=
        hbefore.2.1
      have hsum := Limbs.addCarryBits
        (x := x.toNat) (y := y.toNat) (carry := before.carry.toNat)
        x.isLt y.isLt (by omega)
      have hdstAddr := limbAddr_ofNat dstPtr count (by omega)
      have hsrcAddr := limbAddr_ofNat srcPtr count (by omega)
      let loadedDst := touchMemory before.state (dstPtr + 32 * count) 32
      let loadedSrc := touchMemory loadedDst (srcPtr + 32 * count) 32
      have hstore := memoryLimbs_store_next loadedSrc dstPtr count
        (x + y + before.carry) (by omega)
      simp only [BigArithmetic.addPhase, BigArithmetic.addStep]
      rw [hdstAddr, hsrcAddr]
      change
        memoryLimbs
            (storeWordAt loadedSrc
              (BigArithmetic.limbAddr (BitVec.ofNat 256 dstPtr) count)
              (x + y + before.carry)).memory dstPtr (count + 1) =
              (addNatPhase st.memory dstPtr srcPtr take (count + 1)).digits ∧
          (BigArithmetic.carryWord (x + y) x |||
              BigArithmetic.carryWord (x + y + before.carry) (x + y)).toNat =
              (addNatPhase st.memory dstPtr srcPtr take (count + 1)).carry ∧
          (addNatPhase st.memory dstPtr srcPtr take (count + 1)).carry ≤ 1
      rw [hstore]
      constructor
      · rw [show loadedSrc.memory = before.state.memory by rfl, hbefore.1]
        congr 2
        simp [BitVec.toNat_add, Limbs.radix, hx, hy, hbeforeCarry,
          naturalBefore, addNatPhase]
      · constructor
        · simp only [BitVec.toNat_or, carryWord_toNat, BitVec.toNat_add]
          change ((if (x.toNat + y.toNat) % Limbs.radix < x.toNat then 1 else 0) |||
              if ((x.toNat + y.toNat) % Limbs.radix + before.carry.toNat) %
                  Limbs.radix < (x.toNat + y.toNat) % Limbs.radix then 1 else 0) = _
          rw [hsum]
          simp [addNatPhase, naturalBefore, hx, hy, hbeforeCarry]
        · simp only [addNatPhase]
          rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul Limbs.radix_pos]
          have hxLt := x.isLt
          have hyLt := y.isLt
          have hradix : Limbs.radix = 2 ^ 256 := rfl
          rw [hradix]
          simpa [addNatPhase, naturalBefore, hx, hy, hbeforeCarry] using
            (show x.toNat + y.toNat + before.carry.toNat <
                2 * 2 ^ 256 by omega)

end Challenge.Modexp.Reference.Proofs.Yul.BigMath
