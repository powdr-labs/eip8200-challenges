import Challenge.Modexp.Reference.Proofs.Yul.BigMul
import Challenge.Modexp.Reference.Proofs.Limbs
import Challenge.YulProof.Limbs
import Mathlib.Data.List.GetD

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-!
# Mathematical interpretation of the direct Yul big-number states

The challenge-independent Yul memory representation and its clear/copy frame
facts live in `Challenge.YulProof.Limbs`.  This module re-exports that
interface and connects it to MODEXP's arithmetic lemmas from `Proofs.Limbs`.
-/

namespace Challenge.Modexp.Reference.Proofs.Yul.BigMath

open YulSemantics.EVM
open Challenge.YulProof.EvmState

export Challenge.YulProof.Limbs
  (memoryLimbs Represents length_memoryLimbs memoryLimb_lt
    represents_value_unique
    wordOffset_ofNat memoryLimbs_succ memoryLimbs_store_next
    memoryLimbs_store_disjoint memoryLimbs_clearWordsState
    clearWordsState_represents_zero memoryLimbs_clearWordsState_disjoint
    clearWordsState_preserves loadWord_copyWordsState_source
    memoryLimbs_copyWordsState copyWordsState_represents
    memoryLimbs_copyWordsState_disjoint copyWordsState_preserves)

/-- MODEXP-facing value view of the generic Yul limb representation. -/
theorem value_of_represents {memory : Nat → UInt8} {ptr count value : Nat}
    (hrep : Represents memory ptr count value) :
    Nat.ofDigits Limbs.radix (memoryLimbs memory ptr count) = value := by
  simpa [Limbs.radix, Challenge.YulProof.Limbs.radix] using
    Challenge.YulProof.Limbs.value_of_represents hrep

/-- MODEXP-facing extensional view of the generic Yul limb representation. -/
theorem represents_iff_value {memory : Nat → UInt8} {ptr count value : Nat}
    (hvalue : value < Limbs.radix ^ count) :
    Represents memory ptr count value ↔
      Nat.ofDigits Limbs.radix (memoryLimbs memory ptr count) = value := by
  have hvalue' : value < Challenge.YulProof.Limbs.radix ^ count := by
    simpa [Limbs.radix, Challenge.YulProof.Limbs.radix] using hvalue
  simpa [Limbs.radix, Challenge.YulProof.Limbs.radix] using
    Challenge.YulProof.Limbs.represents_iff_value hvalue'

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
    rw [BitVec.toNat_and]
    have hmask : ((0 - BitVec.ofNat 256 1).toNat) = 2 ^ 256 - 1 := by
      rw [BitVec.toNat_sub]
      change (2 ^ 256 - 1 + 0) % 2 ^ 256 = 2 ^ 256 - 1
      norm_num
    rw [hmask, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt word.isLt]

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
        rw [wordOffset_ofNat ptr count (by omega)]
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
        · rw [wordOffset_ofNat dstPtr count (by omega)]
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
      have hdstAddr := wordOffset_ofNat dstPtr count (by omega)
      have hsrcAddr := wordOffset_ofNat srcPtr count (by omega)
      let loadedDst := touchMemory before.state (dstPtr + 32 * count) 32
      let loadedSrc := touchMemory loadedDst (srcPtr + 32 * count) 32
      have hstore := memoryLimbs_store_next loadedSrc dstPtr count
        (x + y + before.carry) (by omega)
      simp only [BigArithmetic.addPhase, BigArithmetic.addStep]
      rw [hdstAddr, hsrcAddr]
      change
        memoryLimbs
            (storeWordAt loadedSrc
              (wordOffset (BitVec.ofNat 256 dstPtr) count)
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
        simp [BitVec.toNat_add, Limbs.radix,
          Challenge.YulProof.Limbs.radix, hx, hy, hbeforeCarry,
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

/-! ## Subtraction candidate -/

theorem sub_toNat (x y : U256) :
    (x - y).toNat = if x.toNat < y.toNat then
      Limbs.radix + x.toNat - y.toNat else x.toNat - y.toNat := by
  simp only [BitVec.toNat_sub]
  rw [show Limbs.radix = 2 ^ 256 by rfl]
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · have hyx : y.toNat ≤ x.toNat := by omega
    rw [show 2 ^ 256 - y.toNat + x.toNat =
        2 ^ 256 + (x.toNat - y.toNat) by omega, Nat.add_mod,
      Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [Nat.mod_eq_of_lt]
    omega

theorem loadWord_subPhase_region (st : EvmState) (dst modulus : U256)
    (ptr total count j : Nat) (hcount : count ≤ total) (hj : j < total)
    (hfit : 5120 + 32 * count < 2 ^ 256)
    (hdisjoint : 5120 + 32 * total ≤ ptr ∨ ptr + 32 * total ≤ 5120) :
    loadWord (BigArithmetic.subPhase st dst modulus count).state.memory
        (ptr + 32 * j) = loadWord st.memory (ptr + 32 * j) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [BigArithmetic.subPhase]
      simp only [BigArithmetic.subStep, storeWordAt]
      rw [show (5120 : U256) = BitVec.ofNat 256 5120 by rfl]
      rw [YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
      · exact ih (by omega) (by omega)
      · rw [wordOffset_ofNat 5120 count (by omega)]
        rcases hdisjoint with hafter | hbefore
        · left; omega
        · right; omega

theorem loadWord_subPhase_future (st : EvmState) (dst modulus : U256)
    (count j : Nat) (hcount : count ≤ j)
    (hfit : 5120 + 32 * j < 2 ^ 256) :
    loadWord (BigArithmetic.subPhase st dst modulus count).state.memory
        (5120 + 32 * j) = loadWord st.memory (5120 + 32 * j) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [BigArithmetic.subPhase]
      simp only [BigArithmetic.subStep, storeWordAt]
      rw [show (5120 : U256) = BitVec.ofNat 256 5120 by rfl]
      rw [YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
      · exact ih (by omega)
      · left
        rw [wordOffset_ofNat 5120 count (by omega)]
        omega

structure SubNatPhase where
  digits : List Nat
  borrow : Nat

def subNatPhase (memory : Nat → UInt8) (dst modulus : Nat) :
    Nat → SubNatPhase
  | 0 => ⟨[], 0⟩
  | i + 1 =>
      let before := subNatPhase memory dst modulus i
      let x := (loadWord memory (dst + 32 * i)).toNat
      let y := (loadWord memory (modulus + 32 * i)).toNat
      let nextBorrow := if x < y + before.borrow then 1 else 0
      ⟨before.digits ++
        [x + Limbs.radix * nextBorrow - y - before.borrow], nextBorrow⟩

theorem subNatPhase_eq_subDigitLists (memory : Nat → UInt8)
    (dst modulus count : Nat) :
    let natural := subNatPhase memory dst modulus count
    let result := Limbs.subDigitLists (memoryLimbs memory dst count)
      (memoryLimbs memory modulus count) 0
    natural.digits = result.1 ∧ natural.borrow = result.2 := by
  induction count with
  | zero => simp [subNatPhase, memoryLimbs, Limbs.subDigitLists]
  | succ count ih =>
      rw [subNatPhase, memoryLimbs_succ, memoryLimbs_succ,
        Limbs.subDigitLists_append_single (by simp)]
      rcases ih with ⟨hdigits, hborrow⟩
      simp only
      rw [hdigits, hborrow]
      exact ⟨rfl, rfl⟩

theorem subPhase_matches_nat (st : EvmState)
    (dstPtr modulusPtr total count : Nat) (hcount : count ≤ total)
    (hdstfit : dstPtr + 32 * total < 2 ^ 256)
    (hmodfit : modulusPtr + 32 * total < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * total < 2 ^ 256)
    (hdstDisjoint : 5120 + 32 * total ≤ dstPtr ∨
      dstPtr + 32 * total ≤ 5120)
    (hmodDisjoint : 5120 + 32 * total ≤ modulusPtr ∨
      modulusPtr + 32 * total ≤ 5120) :
    let phase := BigArithmetic.subPhase st (BitVec.ofNat 256 dstPtr)
      (BitVec.ofNat 256 modulusPtr) count
    let natural := subNatPhase st.memory dstPtr modulusPtr count
    memoryLimbs phase.state.memory 5120 count = natural.digits ∧
      phase.borrow.toNat = natural.borrow ∧ natural.borrow ≤ 1 := by
  induction count with
  | zero => simp [BigArithmetic.subPhase, subNatPhase, memoryLimbs]
  | succ count ih =>
      have hi : count < total := by omega
      have hbefore := ih (by omega)
      let before := BigArithmetic.subPhase st (BitVec.ofNat 256 dstPtr)
        (BitVec.ofNat 256 modulusPtr) count
      let naturalBefore := subNatPhase st.memory dstPtr modulusPtr count
      let x := loadWord before.state.memory (dstPtr + 32 * count)
      let y := loadWord before.state.memory (modulusPtr + 32 * count)
      let difference := x - y
      let z := difference - before.borrow
      have hx : x = loadWord st.memory (dstPtr + 32 * count) :=
        loadWord_subPhase_region st _ _ dstPtr total count count (by omega) hi
          (by omega) hdstDisjoint
      have hy : y = loadWord st.memory (modulusPtr + 32 * count) :=
        loadWord_subPhase_region st _ _ modulusPtr total count count (by omega) hi
          (by omega) hmodDisjoint
      have hbeforeBorrow : before.borrow.toNat = naturalBefore.borrow :=
        hbefore.2.1
      have hborrowLe : before.borrow.toNat ≤ 1 :=
        hbeforeBorrow.trans_le hbefore.2.2
      have hstep := Limbs.subLimbBits x.isLt y.isLt hborrowLe
      have hz : z.toNat = x.toNat + Limbs.radix *
          (if x.toNat < y.toNat + before.borrow.toNat then 1 else 0) -
          y.toNat - before.borrow.toNat := by
        rw [show z = difference - before.borrow by rfl,
          sub_toNat difference before.borrow,
          show difference.toNat =
            (if x.toNat < y.toNat then Limbs.radix + x.toNat - y.toNat
             else x.toNat - y.toNat) by exact sub_toNat x y]
        exact hstep.1
      have hdstAddr := wordOffset_ofNat dstPtr count (by omega)
      have hmodAddr := wordOffset_ofNat modulusPtr count (by omega)
      have hcandAddr := wordOffset_ofNat 5120 count (by omega)
      let loadedDst := touchMemory before.state (dstPtr + 32 * count) 32
      let loadedMod := touchMemory loadedDst (modulusPtr + 32 * count) 32
      have hstore := memoryLimbs_store_next loadedMod 5120 count z (by omega)
      simp only [BigArithmetic.subPhase, BigArithmetic.subStep]
      rw [show (5120 : U256) = BitVec.ofNat 256 5120 by rfl]
      rw [hdstAddr, hmodAddr]
      change
        memoryLimbs (storeWordAt loadedMod
            (wordOffset (BitVec.ofNat 256 5120) count) z).memory
            5120 (count + 1) =
              (subNatPhase st.memory dstPtr modulusPtr (count + 1)).digits ∧
          (BigArithmetic.carryWord x y |||
              BigArithmetic.carryWord difference before.borrow).toNat =
              (subNatPhase st.memory dstPtr modulusPtr (count + 1)).borrow ∧
          (subNatPhase st.memory dstPtr modulusPtr (count + 1)).borrow ≤ 1
      rw [hstore]
      constructor
      · rw [show loadedMod.memory = before.state.memory by rfl, hbefore.1]
        rw [hz]
        simp [subNatPhase, naturalBefore, hx, hy, hbeforeBorrow]
      · constructor
        · simp only [BitVec.toNat_or, carryWord_toNat]
          rw [show difference.toNat =
              (if x.toNat < y.toNat then Limbs.radix + x.toNat - y.toNat
               else x.toNat - y.toNat) by exact sub_toNat x y]
          rw [hstep.2]
          simp [subNatPhase, naturalBefore, hx, hy, hbeforeBorrow]
        · simp only [subNatPhase]
          split <;> omega

theorem addPhase_value_carry (st : EvmState)
    (dst src count take x y : Nat) (htake : take ≤ 1)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hsrcfit : src + 32 * count < 2 ^ 256)
    (halias : dst = src ∨ dst + 32 * count ≤ src ∨
      src + 32 * count ≤ dst)
    (hdst : Represents st.memory dst count x)
    (hsrc : Represents st.memory src count y) :
    let phase := BigArithmetic.addPhase st (BitVec.ofNat 256 dst)
      (BitVec.ofNat 256 src) (0 - BitVec.ofNat 256 take) count
    Nat.ofDigits Limbs.radix (memoryLimbs phase.state.memory dst count) +
        Limbs.radix ^ count * phase.carry.toNat = x + take * y ∧
      phase.carry.toNat ≤ 1 := by
  let phase := BigArithmetic.addPhase st (BitVec.ofNat 256 dst)
    (BitVec.ofNat 256 src) (0 - BitVec.ofNat 256 take) count
  let natural := addNatPhase st.memory dst src take count
  have hmatch := addPhase_matches_nat st dst src count count take (by omega)
    htake hdstfit hsrcfit halias
  have hcanonical := addNatPhase_eq_addDigitLists st.memory dst src take count
  have hlength : (memoryLimbs st.memory dst count).length =
      ((memoryLimbs st.memory src count).map (take * ·)).length := by simp
  have hvalue := Limbs.addDigitLists_value (carry := 0) hlength
  rw [Limbs.ofDigits_map_mul, Nat.add_zero, value_of_represents hdst,
    value_of_represents hsrc] at hvalue
  dsimp only [phase, natural] at hmatch hcanonical ⊢
  rw [hmatch.1, hcanonical.1, hmatch.2.1, hcanonical.2]
  refine ⟨by simpa using hvalue, ?_⟩
  exact Limbs.addDigitLists_masked_carry_le_one (by simp)
    (fun digit hdigit => memoryLimb_lt _ _ _ hdigit)
    (fun digit hdigit => memoryLimb_lt _ _ _ hdigit) htake

theorem addPhase_represents_wrapped (st : EvmState)
    (dst src count take x y : Nat) (htake : take ≤ 1)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hsrcfit : src + 32 * count < 2 ^ 256)
    (halias : dst = src ∨ dst + 32 * count ≤ src ∨
      src + 32 * count ≤ dst)
    (hdst : Represents st.memory dst count x)
    (hsrc : Represents st.memory src count y) :
    Represents
      (BigArithmetic.addPhase st (BitVec.ofNat 256 dst)
        (BitVec.ofNat 256 src) (0 - BitVec.ofNat 256 take) count).state.memory
      dst count ((x + take * y) % Limbs.radix ^ count) := by
  have hmatch := addPhase_matches_nat st dst src count count take (by omega)
    htake hdstfit hsrcfit halias
  have hcanonical := addNatPhase_eq_addDigitLists st.memory dst src take count
  have hmod := Limbs.addDigitLists_masked_value_mod
    (xs := memoryLimbs st.memory dst count)
    (ys := memoryLimbs st.memory src count) (take := take) (by simp)
  rw [value_of_represents hdst, value_of_represents hsrc] at hmod
  rw [represents_iff_value (Nat.mod_lt _ (pow_pos Limbs.radix_pos _))]
  rw [hmatch.1, hcanonical.1]
  simpa using hmod

theorem subPhase_value_borrow (st : EvmState)
    (dst modulus count x m : Nat)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hmodfit : modulus + 32 * count < 2 ^ 256)
    (hdstDisjoint : 5120 + 32 * count ≤ dst ∨
      dst + 32 * count ≤ 5120)
    (hmodDisjoint : 5120 + 32 * count ≤ modulus ∨
      modulus + 32 * count ≤ 5120)
    (hdst : Represents st.memory dst count x)
    (hmodulus : Represents st.memory modulus count m) :
    let phase := BigArithmetic.subPhase st (BitVec.ofNat 256 dst)
      (BitVec.ofNat 256 modulus) count
    Nat.ofDigits Limbs.radix (memoryLimbs phase.state.memory 5120 count) + m =
        x + Limbs.radix ^ count * phase.borrow.toNat ∧
      phase.borrow.toNat ≤ 1 := by
  let phase := BigArithmetic.subPhase st (BitVec.ofNat 256 dst)
    (BitVec.ofNat 256 modulus) count
  let natural := subNatPhase st.memory dst modulus count
  have hmatch := subPhase_matches_nat st dst modulus count count (by omega)
    hdstfit hmodfit (by omega) hdstDisjoint hmodDisjoint
  have hcanonical := subNatPhase_eq_subDigitLists st.memory dst modulus count
  have hlength : (memoryLimbs st.memory dst count).length =
      (memoryLimbs st.memory modulus count).length := by simp
  have hvalue := Limbs.subDigitLists_value (borrow := 0) hlength
    (fun digit hdigit => memoryLimb_lt _ _ _ hdigit)
    (fun digit hdigit => memoryLimb_lt _ _ _ hdigit) (by omega)
  rw [value_of_represents hdst, value_of_represents hmodulus,
    Nat.add_zero] at hvalue
  dsimp only [phase, natural] at hmatch hcanonical ⊢
  rw [hmatch.1, hcanonical.1, hmatch.2.1, hcanonical.2]
  refine ⟨by simpa using hvalue, ?_⟩
  exact Limbs.subDigitLists_borrow_le_one (by simp) (by omega)

/-! ## Final conditional selection -/

theorem selectWord_eq (sum reduced useSub : U256) (huse : useSub.toNat ≤ 1) :
    (reduced &&& (0 - useSub)) ||| (sum &&& ~~~(0 - useSub)) =
      if useSub = 0 then sum else reduced := by
  have hcases : useSub.toNat = 0 ∨ useSub.toNat = 1 := by omega
  rcases hcases with hzero | hone
  · have : useSub = 0 := BitVec.eq_of_toNat_eq hzero
    subst useSub
    change (reduced &&& (0 : U256)) ||| (sum &&& BitVec.allOnes 256) = sum
    have hz : reduced &&& (0 : U256) = 0 := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_and]
    rw [hz, BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_or]
  · have : useSub = 1 := BitVec.eq_of_toNat_eq hone
    subst useSub
    change (reduced &&& BitVec.allOnes 256) ||| (sum &&& (0 : U256)) = reduced
    have hz : sum &&& (0 : U256) = 0 := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_and]
    rw [BitVec.and_allOnes, hz]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_or]

theorem loadWord_selectPhase_future (st : EvmState) (dst mask : U256)
    (dstPtr count j : Nat) (hdst : dst = BitVec.ofNat 256 dstPtr)
    (hcount : count ≤ j) (hfit : dstPtr + 32 * j < 2 ^ 256) :
    loadWord (BigArithmetic.selectPhase st dst mask count).memory
        (dstPtr + 32 * j) = loadWord st.memory (dstPtr + 32 * j) := by
  subst dst
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [BigArithmetic.selectPhase]
      simp only [BigArithmetic.selectStep, storeWordAt]
      rw [YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
      · exact ih (by omega)
      · left
        rw [wordOffset_ofNat dstPtr count (by omega)]
        omega

theorem loadWord_selectPhase_candidate (st : EvmState) (dst mask : U256)
    (dstPtr total count j : Nat) (hdst : dst = BitVec.ofNat 256 dstPtr)
    (hcount : count ≤ total) (hj : j < total)
    (hdstfit : dstPtr + 32 * total < 2 ^ 256)
    (hdisjoint : dstPtr + 32 * total ≤ 5120 ∨
      5120 + 32 * total ≤ dstPtr) :
    loadWord (BigArithmetic.selectPhase st dst mask count).memory
        (5120 + 32 * j) = loadWord st.memory (5120 + 32 * j) := by
  subst dst
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [BigArithmetic.selectPhase]
      simp only [BigArithmetic.selectStep, storeWordAt]
      rw [YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
      · exact ih (by omega)
      · rw [wordOffset_ofNat dstPtr count (by omega)]
        rcases hdisjoint with hbefore | hafter
        · left; omega
        · right; omega

theorem selectPhase_memoryLimbs (st : EvmState)
    (dst count : Nat) (useSub : U256) (huse : useSub.toNat ≤ 1)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ dst) :
    memoryLimbs
        (BigArithmetic.selectPhase st (BitVec.ofNat 256 dst)
          (0 - useSub) count).memory dst count =
      if useSub = 0 then memoryLimbs st.memory dst count
      else memoryLimbs st.memory 5120 count := by
  induction count with
  | zero => simp [BigArithmetic.selectPhase, memoryLimbs]
  | succ count ih =>
      have hi : count < count + 1 := by omega
      let before := BigArithmetic.selectPhase st (BitVec.ofNat 256 dst)
        (0 - useSub) count
      let sum := loadWord before.memory (dst + 32 * count)
      let reduced := loadWord before.memory (5120 + 32 * count)
      let loadedSum := touchMemory before (dst + 32 * count) 32
      let loadedReduced := touchMemory loadedSum (5120 + 32 * count) 32
      let chosen := (reduced &&& (0 - useSub)) |||
        (sum &&& ~~~(0 - useSub))
      have hsum : sum = loadWord st.memory (dst + 32 * count) :=
        loadWord_selectPhase_future st _ _ dst count count rfl (by omega)
          (by omega)
      have hreduced : reduced = loadWord st.memory (5120 + 32 * count) :=
        loadWord_selectPhase_candidate st _ _ dst (count + 1) count count rfl
          (by omega) hi (by omega) hdisjoint
      have hchosen : chosen = if useSub = 0 then sum else reduced :=
        selectWord_eq sum reduced useSub huse
      have hstore := memoryLimbs_store_next loadedReduced dst count chosen
        (by omega)
      simp only [BigArithmetic.selectPhase, BigArithmetic.selectStep]
      rw [wordOffset_ofNat dst count (by omega)]
      rw [show (5120 : U256) = BitVec.ofNat 256 5120 by rfl,
        wordOffset_ofNat 5120 count (by omega)]
      change memoryLimbs
          (storeWordAt loadedReduced
            (wordOffset (BitVec.ofNat 256 dst) count) chosen).memory
            dst (count + 1) = _
      rw [hstore, show loadedReduced.memory = before.memory by rfl,
        ih (by omega) (by rcases hdisjoint with h | h <;> omega)]
      rw [memoryLimbs_succ, memoryLimbs_succ, hchosen, hsum, hreduced]
      split <;> rfl

theorem memoryLimbs_addPhase_disjoint (st : EvmState) (dst src mask : U256)
    (dstPtr ptr total count : Nat) (hdst : dst = BitVec.ofNat 256 dstPtr)
    (hcount : count ≤ total) (hdstfit : dstPtr + 32 * total < 2 ^ 256)
    (hdisjoint : dstPtr + 32 * total ≤ ptr ∨
      ptr + 32 * total ≤ dstPtr) :
    memoryLimbs (BigArithmetic.addPhase st dst src mask count).state.memory
        ptr total = memoryLimbs st.memory ptr total := by
  subst dst
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [BigArithmetic.addPhase]
      simp only [BigArithmetic.addStep]
      rw [memoryLimbs_store_disjoint]
      · exact ih (by omega)
      · rw [wordOffset_ofNat dstPtr count (by omega)]
        rcases hdisjoint with hbefore | hafter
        · left; omega
        · right; omega

theorem memoryLimbs_subPhase_region (st : EvmState) (dst modulus : U256)
    (ptr total count : Nat) (hcount : count ≤ total)
    (hfit : 5120 + 32 * count < 2 ^ 256)
    (hdisjoint : 5120 + 32 * total ≤ ptr ∨
      ptr + 32 * total ≤ 5120) :
    memoryLimbs (BigArithmetic.subPhase st dst modulus count).state.memory
        ptr total = memoryLimbs st.memory ptr total := by
  unfold memoryLimbs
  apply List.map_congr_left
  intro j hj
  rw [loadWord_subPhase_region st dst modulus ptr total count j hcount
    (by simpa using hj) hfit hdisjoint]

/-- The exact mathematical contract needed by both modular multiplication
and the big-path base conversion.  Aliasing `dst = src` is explicitly
supported (the doubling used by `mulModBig`). -/
theorem addMaskedModState_represents (st : EvmState)
    (dst src modulus count take x y m : Nat) (hcount : count ≤ 32)
    (htake : take ≤ 1) (hmpos : 0 < m)
    (hx : x < m) (hy : y ≤ m)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hsrcfit : src + 32 * count < 2 ^ 256)
    (hmodfit : modulus + 32 * count < 2 ^ 256)
    (hdst : Represents st.memory dst count x)
    (hsrc : Represents st.memory src count y)
    (hmodulus : Represents st.memory modulus count m)
    (halias : dst = src ∨ dst + 32 * count ≤ src ∨
      src + 32 * count ≤ dst)
    (hdstCandidate : dst + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ dst)
    (hmodCandidate : modulus + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ modulus)
    (hdstModulus : dst + 32 * count ≤ modulus ∨
      modulus + 32 * count ≤ dst) :
    Represents
      (BigArithmetic.addMaskedModState st (BitVec.ofNat 256 dst)
        (BitVec.ofNat 256 src) (BitVec.ofNat 256 take)
        (BitVec.ofNat 256 modulus) count).memory
      dst count ((x + take * y) % m) := by
  let bound := Limbs.radix ^ count
  let total := x + take * y
  let added := BigArithmetic.addPhase st (BitVec.ofNat 256 dst)
    (BitVec.ofNat 256 src) (0 - BitVec.ofNat 256 take) count
  let subtracted := BigArithmetic.subPhase added.state
    (BitVec.ofNat 256 dst) (BitVec.ofNat 256 modulus) count
  let useSub := added.carry ||| YulSemantics.EVM.b2w (subtracted.borrow = 0)
  have hcandfit : 5120 + 32 * count < 2 ^ 256 := by omega
  have haddValue := addPhase_value_carry st dst src count take x y htake
    hdstfit hsrcfit halias hdst hsrc
  have haddRep := addPhase_represents_wrapped st dst src count take x y htake
    hdstfit hsrcfit halias hdst hsrc
  have haddModulus : Represents added.state.memory modulus count m := by
    refine ⟨hmodulus.1, ?_⟩
    exact (memoryLimbs_addPhase_disjoint st _ _ _ dst modulus count count rfl
      (by omega) hdstfit hdstModulus).trans hmodulus.2
  have hsubValue := subPhase_value_borrow added.state dst modulus count
    ((x + take * y) % bound) m hdstfit hmodfit
    (by rcases hdstCandidate with h | h <;> simp_all [bound])
    (by rcases hmodCandidate with h | h <;> simp_all [bound])
    (by simpa [added, bound] using haddRep) haddModulus
  have hsubDst : memoryLimbs subtracted.state.memory dst count =
      memoryLimbs added.state.memory dst count := by
    exact memoryLimbs_subPhase_region added.state _ _ dst count count (by omega)
      hcandfit (by rcases hdstCandidate with h | h <;> omega)
  have hboundPos : 0 < bound := pow_pos Limbs.radix_pos count
  have hwrappedLt : total % bound < bound := Nat.mod_lt _ hboundPos
  have haddEq : Nat.ofDigits Limbs.radix
        (memoryLimbs added.state.memory dst count) +
      bound * added.carry.toNat = total := by
    simpa [added, bound, total] using haddValue.1
  have hsubEq : Nat.ofDigits Limbs.radix
        (memoryLimbs subtracted.state.memory 5120 count) + m =
      total % bound + bound * subtracted.borrow.toNat := by
    simpa [subtracted, bound, total] using hsubValue.1
  have haddedValue : Nat.ofDigits Limbs.radix
      (memoryLimbs added.state.memory dst count) = total % bound := by
    simpa [added, total, bound] using value_of_represents haddRep
  have hcandidateLt : Nat.ofDigits Limbs.radix
      (memoryLimbs subtracted.state.memory 5120 count) < bound := by
    have h := Nat.ofDigits_lt_base_pow_length Limbs.radix_gt_one
      (fun digit hdigit => memoryLimb_lt subtracted.state.memory 5120 count hdigit)
    simpa [bound] using h
  have hcarryLe : added.carry.toNat ≤ 1 := by
    simpa [added] using haddValue.2
  have hborrowLe : subtracted.borrow.toNat ≤ 1 := by
    simpa [subtracted] using hsubValue.2
  have hb2wLe : (YulSemantics.EVM.b2w (subtracted.borrow = 0)).toNat ≤ 1 := by
    simp only [YulSemantics.EVM.b2w]
    split <;> simp
  have huseLe : useSub.toNat ≤ 1 := by
    simp only [useSub, BitVec.toNat_or]
    interval_cases added.carry.toNat <;>
      interval_cases (YulSemantics.EVM.b2w (subtracted.borrow = 0)).toNat <;>
      norm_num
  have hselect := selectPhase_memoryLimbs subtracted.state dst count useSub
    huseLe hdstfit hdstCandidate
  simp only [BigArithmetic.addMaskedModState]
  rw [represents_iff_value ((Nat.mod_lt _ hmpos).trans hmodulus.1)]
  change Nat.ofDigits Limbs.radix
      (memoryLimbs
        (BigArithmetic.selectPhase subtracted.state (BitVec.ofNat 256 dst)
          (0 - useSub) count).memory dst count) = total % m
  rw [hselect]
  have htotalLt : total < 2 * m :=
    Limbs.masked_sum_lt_twice_of_le hx hy htake
  rw [Limbs.mod_eq_cond_sub htotalLt]
  split_ifs with huseZero htotalSmall
  · have hcarryZero : added.carry.toNat = 0 := by
      by_contra hne
      have : added.carry.toNat = 1 := by omega
      have hu : useSub.toNat ≠ 0 := by
        simp [useSub, BitVec.toNat_or, this]
      exact hu (congrArg BitVec.toNat huseZero)
    have hborrowNe : subtracted.borrow ≠ 0 := by
      intro hb
      have : useSub.toNat ≠ 0 := by
        simp [useSub, hb, YulSemantics.EVM.b2w]
      exact this (congrArg BitVec.toNat huseZero)
    have hborrowOne : subtracted.borrow.toNat = 1 := by
      have : subtracted.borrow.toNat ≠ 0 := by
        intro h
        exact hborrowNe (BitVec.eq_of_toNat_eq h)
      omega
    have haddDigits : Nat.ofDigits Limbs.radix
        (memoryLimbs added.state.memory dst count) = total := by
      simpa [hcarryZero] using haddEq
    rw [hsubDst, haddDigits]
  · exfalso
    have hcarryZero : added.carry.toNat = 0 := by
      by_contra hne
      have : added.carry.toNat = 1 := by omega
      have hu : useSub.toNat ≠ 0 := by
        simp [useSub, BitVec.toNat_or, this]
      exact hu (congrArg BitVec.toNat huseZero)
    have hborrowNe : subtracted.borrow ≠ 0 := by
      intro hb
      have hu : useSub.toNat ≠ 0 := by
        simp [useSub, hb, YulSemantics.EVM.b2w]
      exact hu (congrArg BitVec.toNat huseZero)
    have hborrowOne : subtracted.borrow.toNat = 1 := by
      have : subtracted.borrow.toNat ≠ 0 := by
        intro h
        exact hborrowNe (BitVec.eq_of_toNat_eq h)
      omega
    simp [hcarryZero, hborrowOne] at haddEq hsubEq
    omega
  · have huseNonzero : useSub.toNat ≠ 0 := by
      intro h
      exact huseZero (BitVec.eq_of_toNat_eq h)
    have hcarryOrBorrow : added.carry.toNat = 1 ∨
        subtracted.borrow.toNat = 0 := by
      by_cases hb : subtracted.borrow.toNat = 0
      · right; exact hb
      · left
        have hb2wZero : (YulSemantics.EVM.b2w
            (subtracted.borrow = 0)).toNat = 0 := by
          simp only [YulSemantics.EVM.b2w]
          split
          · rename_i htrue
            have hword : subtracted.borrow = 0 := by
              exact of_decide_eq_true htrue
            exact (hb (by simpa using congrArg BitVec.toNat hword)).elim
          · rfl
        have hcNonzero : added.carry.toNat ≠ 0 := by
          change (added.carry ||| YulSemantics.EVM.b2w
            (subtracted.borrow = 0)).toNat ≠ 0 at huseNonzero
          rw [BitVec.toNat_or, hb2wZero, Nat.or_zero] at huseNonzero
          exact huseNonzero
        omega
    rcases hcarryOrBorrow with hcarry | hborrow
    · simp [hcarry] at haddEq
      have hmBound : m < bound := by
        simpa [bound, Limbs.radix, Challenge.YulProof.Limbs.radix] using
          hmodulus.1
      omega
    · simp [hborrow] at hsubEq
      have hmBound : m < bound := by
        simpa [bound, Limbs.radix, Challenge.YulProof.Limbs.radix] using
          hmodulus.1
      have htotalBound : total < bound := by omega
      rw [Nat.mod_eq_of_lt htotalBound] at hsubEq
      omega
  · have huseNonzero : useSub.toNat ≠ 0 := by
      intro h
      exact huseZero (BitVec.eq_of_toNat_eq h)
    have hcarryOrBorrow : added.carry.toNat = 1 ∨
        subtracted.borrow.toNat = 0 := by
      simp only [useSub, BitVec.toNat_or] at huseNonzero
      by_cases hb : subtracted.borrow.toNat = 0
      · right; exact hb
      · left
        have hb2wZero : (YulSemantics.EVM.b2w
            (subtracted.borrow = 0)).toNat = 0 := by
          simp only [YulSemantics.EVM.b2w]
          split
          · rename_i htrue
            have hword : subtracted.borrow = 0 := by
              exact of_decide_eq_true htrue
            exact (hb (by simpa using congrArg BitVec.toNat hword)).elim
          · rfl
        have hcNonzero : added.carry.toNat ≠ 0 := by
          rw [hb2wZero, Nat.or_zero] at huseNonzero
          exact huseNonzero
        omega
    rcases hcarryOrBorrow with hcarry | hborrow
    · have hmBound : m < bound := by
        simpa [bound, Limbs.radix, Challenge.YulProof.Limbs.radix] using
          hmodulus.1
      interval_cases hb : subtracted.borrow.toNat
      · simp [hcarry, hb] at haddEq hsubEq
        omega
      · simp [hcarry, hb] at haddEq hsubEq
        omega
    · have hmBound : m < bound := by
        simpa [bound, Limbs.radix, Challenge.YulProof.Limbs.radix] using
          hmodulus.1
      interval_cases hc : added.carry.toNat
      · simp [hborrow, hc] at haddEq hsubEq
        omega
      · simp [hborrow, hc] at haddEq hsubEq
        omega

theorem memoryLimbs_selectPhase_disjoint (st : EvmState) (dst mask : U256)
    (dstPtr ptr total count : Nat) (hdst : dst = BitVec.ofNat 256 dstPtr)
    (hcount : count ≤ total) (hdstfit : dstPtr + 32 * total < 2 ^ 256)
    (hdisjoint : dstPtr + 32 * total ≤ ptr ∨
      ptr + 32 * total ≤ dstPtr) :
    memoryLimbs (BigArithmetic.selectPhase st dst mask count).memory ptr total =
      memoryLimbs st.memory ptr total := by
  subst dst
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [BigArithmetic.selectPhase]
      simp only [BigArithmetic.selectStep]
      rw [memoryLimbs_store_disjoint]
      · exact ih (by omega)
      · rw [wordOffset_ofNat dstPtr count (by omega)]
        rcases hdisjoint with hbefore | hafter
        · left; omega
        · right; omega

theorem addMaskedModState_preserves (st : EvmState)
    (dst src modulus count take ptr value : Nat)
    (hcount : count ≤ 32)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hptrDst : dst + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ dst)
    (hptrCandidate : 5120 + 32 * count ≤ ptr ∨
      ptr + 32 * count ≤ 5120)
    (hrep : Represents st.memory ptr count value) :
    Represents
      (BigArithmetic.addMaskedModState st (BitVec.ofNat 256 dst)
        (BitVec.ofNat 256 src) (BitVec.ofNat 256 take)
        (BitVec.ofNat 256 modulus) count).memory
      ptr count value := by
  let added := BigArithmetic.addPhase st (BitVec.ofNat 256 dst)
    (BitVec.ofNat 256 src) (0 - BitVec.ofNat 256 take) count
  let subtracted := BigArithmetic.subPhase added.state
    (BitVec.ofNat 256 dst) (BitVec.ofNat 256 modulus) count
  have hadd : memoryLimbs added.state.memory ptr count =
      memoryLimbs st.memory ptr count :=
    memoryLimbs_addPhase_disjoint st _ _ _ dst ptr count count rfl
      (by omega) hdstfit hptrDst
  have hsub : memoryLimbs subtracted.state.memory ptr count =
      memoryLimbs added.state.memory ptr count :=
    memoryLimbs_subPhase_region added.state _ _ ptr count count (by omega)
      (by omega : 5120 + 32 * count < 2 ^ 256) hptrCandidate
  have hselect : memoryLimbs
      (BigArithmetic.addMaskedModState st (BitVec.ofNat 256 dst)
        (BitVec.ofNat 256 src) (BitVec.ofNat 256 take)
        (BitVec.ofNat 256 modulus) count).memory
      ptr count = memoryLimbs subtracted.state.memory ptr count := by
    simp only [BigArithmetic.addMaskedModState]
    exact memoryLimbs_selectPhase_disjoint subtracted.state _ _ dst ptr count
      count rfl (by omega) hdstfit hptrDst
  exact ⟨hrep.1, hselect.trans (hsub.trans (hadd.trans hrep.2))⟩

/-! ## Modular multiplication -/

def wordBits (word : U256) (length : Nat) : List Nat :=
  (List.range length).map fun j => (BigMul.multiplierBit word j).toNat

theorem multiplierBit_toNat_le_one (word : U256) (j : Nat) (hj : j < 256) :
    (BigMul.multiplierBit word j).toNat ≤ 1 := by
  rw [BigMul.multiplierBit, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat j 256,
    Nat.mod_eq_of_lt (hj.trans (by norm_num : 256 < 2 ^ 256))]
  rw [show BitVec.toNat (1 : U256) = 1 by decide]
  exact Nat.and_le_right

theorem multiplierBit_toNat (word : U256) (j : Nat) (hj : j < 256) :
    (BigMul.multiplierBit word j).toNat = (word.toNat >>> j) &&& 1 := by
  rw [BigMul.multiplierBit, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat j 256,
    Nat.mod_eq_of_lt (hj.trans (by norm_num : 256 < 2 ^ 256))]
  rw [show BitVec.toNat (1 : U256) = 1 by decide]

theorem wordBits_eq_digitsAppend (word : U256) :
    wordBits word 256 = Nat.digitsAppend 2 256 word.toNat := by
  apply List.ext_get
  · simp [wordBits,
      Nat.length_digitsAppend (n := word.toNat) (by norm_num) 256 word.isLt]
  · intro j hleft hright
    have hj : j < 256 := by simpa [wordBits] using hleft
    have hleftValue : (wordBits word 256).get ⟨j, hleft⟩ =
        (BigMul.multiplierBit word j).toNat := by simp [wordBits]
    rw [hleftValue, multiplierBit_toNat word j hj, Nat.and_one_is_mod]
    have hrightValue :
        (Nat.digitsAppend 2 256 word.toNat).get ⟨j, hright⟩ =
          (Nat.digitsAppend 2 256 word.toNat).getD j 0 :=
      (List.getD_eq_getElem (Nat.digitsAppend 2 256 word.toNat) 0 hright).symm
    rw [hrightValue]
    have hpadded : (Nat.digitsAppend 2 256 word.toNat).getD j 0 =
        (Nat.digits 2 word.toNat).getD j 0 := by
      rw [Nat.digitsAppend]
      by_cases hdigit : j < (Nat.digits 2 word.toNat).length
      · rw [List.getD_append _ _ _ _ hdigit]
      · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hdigit),
          List.getD_eq_default _ _ (Nat.le_of_not_gt hdigit)]
        simp [List.getD_eq_getElem?_getD]
    rw [hpadded, Nat.getD_digits word.toNat j (by omega),
      Nat.shiftRight_eq_div_pow]

theorem value_wordBits (word : U256) :
    Nat.ofDigits 2 (wordBits word 256) = word.toNat := by
  rw [wordBits_eq_digitsAppend, Nat.digitsAppend,
    Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]

theorem wordBits_succ (word : U256) (length : Nat) :
    wordBits word (length + 1) =
      wordBits word length ++ [(BigMul.multiplierBit word length).toNat] := by
  simp [wordBits, List.range_succ]

def limbBits (memory : Nat → UInt8) (ptr steps : Nat) : List Nat :=
  (List.range steps).flatMap fun i =>
    wordBits (loadWord memory (ptr + 32 * i)) 256

theorem limbBits_succ (memory : Nat → UInt8) (ptr steps : Nat) :
    limbBits memory ptr (steps + 1) =
      limbBits memory ptr steps ++
        wordBits (loadWord memory (ptr + 32 * steps)) 256 := by
  simp [limbBits, List.range_succ]

@[simp] theorem length_limbBits (memory : Nat → UInt8)
    (ptr steps : Nat) :
    (limbBits memory ptr steps).length = 256 * steps := by
  simp [limbBits, wordBits]
  omega

theorem value_limbBits (memory : Nat → UInt8) (ptr count : Nat) :
    Nat.ofDigits 2 (limbBits memory ptr count) =
      Nat.ofDigits Limbs.radix (memoryLimbs memory ptr count) := by
  induction count with
  | zero => simp [limbBits, memoryLimbs]
  | succ count ih =>
      rw [limbBits_succ, Nat.ofDigits_append, ih, value_wordBits]
      simp [memoryLimbs, List.range_succ, Nat.ofDigits_append,
        Limbs.radix, Challenge.YulProof.Limbs.radix, Nat.pow_mul]

theorem loadWord_eq_of_represents (left right : Nat → UInt8)
    (ptr count value i : Nat) (hi : i < count)
    (hleft : Represents left ptr count value)
    (hright : Represents right ptr count value) :
    loadWord left (ptr + 32 * i) = loadWord right (ptr + 32 * i) := by
  have hlists : memoryLimbs left ptr count = memoryLimbs right ptr count :=
    hleft.2.trans hright.2.symm
  have hget := congrArg (fun digits => digits[i]?) hlists
  have htoNat : (loadWord left (ptr + 32 * i)).toNat =
      (loadWord right (ptr + 32 * i)).toNat := by
    simpa [memoryLimbs, hi] using hget
  exact BitVec.eq_of_toNat_eq htoNat

theorem mulBitStep_represents (st : EvmState) (word : U256)
    (j count acc addend m : Nat) (hj : j < 256)
    (hcount : count ≤ 32) (hmpos : 0 < m)
    (hacc : Represents st.memory 3072 count acc)
    (haddend : Represents st.memory 4096 count addend)
    (hmodulus : Represents st.memory 0 count m)
    (haccReduced : acc < m) (haddendReduced : addend < m) :
    let bit := (BigMul.multiplierBit word j).toNat
    let after := BigMul.mulBitStep 3072 0 (BitVec.ofNat 256 count) word j st
    Represents after.memory 3072 count ((acc + bit * addend) % m) ∧
      Represents after.memory 4096 count ((addend + addend) % m) ∧
      Represents after.memory 0 count m := by
  let bit := (BigMul.multiplierBit word j).toNat
  let afterAdd := BigArithmetic.addMaskedModState st 3072 4096
    (BigMul.multiplierBit word j) 0 count
  let after := BigArithmetic.addMaskedModState afterAdd 4096 4096 1 0 count
  have hbit : BigMul.multiplierBit word j = BitVec.ofNat 256 bit :=
    (BitVec.eq_of_toNat_eq (by simp [bit])).symm
  have hbitLe : bit ≤ 1 := multiplierBit_toNat_le_one word j hj
  have hafterAcc : Represents afterAdd.memory 3072 count
      ((acc + bit * addend) % m) := by
    simpa [afterAdd, hbit] using
      addMaskedModState_represents st 3072 4096 0 count bit acc addend m
        hcount hbitLe hmpos haccReduced haddendReduced.le (by omega) (by omega)
        (by omega) hacc haddend hmodulus (by right; left; omega)
        (by left; omega) (by left; omega) (by right; omega)
  have hafterAddend : Represents afterAdd.memory 4096 count addend := by
    simpa [afterAdd, hbit] using
      addMaskedModState_preserves st 3072 4096 0 count bit 4096 addend
        hcount (by omega) (by left; omega) (by right; omega) haddend
  have hafterModulus : Represents afterAdd.memory 0 count m := by
    simpa [afterAdd, hbit] using
      addMaskedModState_preserves st 3072 4096 0 count bit 0 m hcount
        (by omega) (by right; omega) (by right; omega) hmodulus
  have hdoubleAddend : Represents after.memory 4096 count
      ((addend + addend) % m) := by
    simpa [after] using
      addMaskedModState_represents afterAdd 4096 4096 0 count 1 addend addend m
        hcount (by omega) hmpos haddendReduced haddendReduced.le (by omega)
        (by omega) (by omega) hafterAddend hafterAddend hafterModulus
        (by left; rfl) (by left; omega) (by left; omega) (by right; omega)
  have hdoubleAcc : Represents after.memory 3072 count
      ((acc + bit * addend) % m) := by
    exact addMaskedModState_preserves afterAdd 4096 4096 0 count 1 3072
      ((acc + bit * addend) % m) hcount (by omega) (by right; omega)
      (by right; omega) hafterAcc
  have hdoubleModulus : Represents after.memory 0 count m := by
    exact addMaskedModState_preserves afterAdd 4096 4096 0 count 1 0 m hcount
      (by omega) (by right; omega) (by right; omega) hafterModulus
  have hn : (BitVec.ofNat 256 count).toNat = count := by
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hcount.trans_lt (by norm_num : 32 < 2 ^ 256))]
  have hstate : BigMul.mulBitStep 3072 0 (BitVec.ofNat 256 count) word j st =
      after := by
    simp only [BigMul.mulBitStep, hn]
    dsimp only [after, afterAdd]
  change Represents
      (BigMul.mulBitStep 3072 0 (BitVec.ofNat 256 count) word j st).memory
        3072 count ((acc + bit * addend) % m) ∧
    Represents
      (BigMul.mulBitStep 3072 0 (BitVec.ofNat 256 count) word j st).memory
        4096 count ((addend + addend) % m) ∧
    Represents
      (BigMul.mulBitStep 3072 0 (BitVec.ofNat 256 count) word j st).memory
        0 count m
  rw [hstate]
  exact ⟨hdoubleAcc, hdoubleAddend, hdoubleModulus⟩

theorem mulBitStep_preserves (st : EvmState) (word : U256)
    (j count ptr value : Nat) (hcount : count ≤ 32)
    (hptrOut : 3072 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 3072)
    (hptrAddend : 4096 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 4096)
    (hptrCandidate : 5120 + 32 * count ≤ ptr ∨
      ptr + 32 * count ≤ 5120)
    (hrep : Represents st.memory ptr count value) :
    Represents
      (BigMul.mulBitStep 3072 0 (BitVec.ofNat 256 count) word j st).memory
      ptr count value := by
  let bit := (BigMul.multiplierBit word j).toNat
  let afterAdd := BigArithmetic.addMaskedModState st 3072 4096
    (BigMul.multiplierBit word j) 0 count
  have hbit : BigMul.multiplierBit word j = BitVec.ofNat 256 bit :=
    (BitVec.eq_of_toNat_eq (by simp [bit])).symm
  have hafter : Represents afterAdd.memory ptr count value := by
    simpa [afterAdd, hbit] using
      addMaskedModState_preserves st 3072 4096 0 count bit ptr value hcount
        (by omega) hptrOut hptrCandidate hrep
  have hfinal : Represents
      (BigArithmetic.addMaskedModState afterAdd 4096 4096 1 0 count).memory
      ptr count value :=
    addMaskedModState_preserves afterAdd 4096 4096 0 count 1 ptr value
      hcount (by omega) hptrAddend hptrCandidate hafter
  have hn : (BitVec.ofNat 256 count).toNat = count := by
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hcount.trans_lt (by norm_num : 32 < 2 ^ 256))]
  simpa [BigMul.mulBitStep, hn, afterAdd] using hfinal

theorem mulBitPrefix_preserves (st : EvmState) (word : U256)
    (steps count ptr value : Nat) (hsteps : steps ≤ 256)
    (hcount : count ≤ 32)
    (hptrOut : 3072 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 3072)
    (hptrAddend : 4096 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 4096)
    (hptrCandidate : 5120 + 32 * count ≤ ptr ∨
      ptr + 32 * count ≤ 5120)
    (hrep : Represents st.memory ptr count value) :
    Represents
      (BigMul.mulBitPrefix 3072 0 (BitVec.ofNat 256 count) word steps st).memory
      ptr count value := by
  induction steps with
  | zero => simpa [BigMul.mulBitPrefix] using hrep
  | succ steps ih =>
      have hbefore := ih (by omega)
      simpa [BigMul.mulBitPrefix] using
        mulBitStep_preserves
          (BigMul.mulBitPrefix 3072 0 (BitVec.ofNat 256 count) word steps st)
          word steps count ptr value hcount hptrOut hptrAddend
          hptrCandidate hbefore

theorem mulBitPrefix_represents (st : EvmState) (word : U256)
    (steps count acc addend m : Nat) (hsteps : steps ≤ 256)
    (hcount : count ≤ 32) (hmpos : 0 < m)
    (hacc : Represents st.memory 3072 count acc)
    (haddend : Represents st.memory 4096 count addend)
    (hmodulus : Represents st.memory 0 count m)
    (haccReduced : acc < m) (haddendReduced : addend < m) :
    let progress := BigMul.mulBitPrefix 3072 0
      (BitVec.ofNat 256 count) word steps st
    let result := Algorithm.mulBits m acc addend (wordBits word steps)
    Represents progress.memory 3072 count result.1 ∧
      Represents progress.memory 4096 count result.2 ∧
      Represents progress.memory 0 count m := by
  induction steps with
  | zero =>
      simp [BigMul.mulBitPrefix, wordBits, Algorithm.mulBits, hacc, haddend,
        hmodulus]
  | succ steps ih =>
      have hsteps' : steps ≤ 256 := by omega
      let before := BigMul.mulBitPrefix 3072 0
        (BitVec.ofNat 256 count) word steps st
      let beforeResult := Algorithm.mulBits m acc addend (wordBits word steps)
      have hbefore := ih hsteps'
      have hbeforeReduced := Algorithm.mulBits_lt (wordBits word steps) hmpos
        haccReduced haddendReduced
      have hstep := mulBitStep_represents before word steps count
        beforeResult.1 beforeResult.2 m (by omega) hcount hmpos hbefore.1
        hbefore.2.1 hbefore.2.2 hbeforeReduced.1 hbeforeReduced.2
      simpa [BigMul.mulBitPrefix, wordBits_succ, Algorithm.mulBits_append,
        Algorithm.mulBits, before, beforeResult] using hstep

theorem mulLimbPrefix_represents (st : EvmState)
    (bPtr count steps acc addend bValue m : Nat)
    (hsteps : steps ≤ count) (hcount : count ≤ 32)
    (hbPtr : bPtr + 32 * count ≤ 3072) (hmpos : 0 < m)
    (hacc : Represents st.memory 3072 count acc)
    (haddend : Represents st.memory 4096 count addend)
    (hb : Represents st.memory bPtr count bValue)
    (hmodulus : Represents st.memory 0 count m)
    (haccReduced : acc < m) (haddendReduced : addend < m) :
    let progress := BigMul.mulLimbPrefix (BitVec.ofNat 256 bPtr) 3072 0
      (BitVec.ofNat 256 count) steps st
    let result := Algorithm.mulBits m acc addend
      (limbBits st.memory bPtr steps)
    Represents progress.memory 3072 count result.1 ∧
      Represents progress.memory 4096 count result.2 ∧
      Represents progress.memory bPtr count bValue ∧
      Represents progress.memory 0 count m := by
  induction steps with
  | zero =>
      simp [BigMul.mulLimbPrefix, limbBits, Algorithm.mulBits, hacc, haddend,
        hb, hmodulus]
  | succ steps ih =>
      have hsteps' : steps ≤ count := by omega
      have hi : steps < count := by omega
      let before := BigMul.mulLimbPrefix (BitVec.ofNat 256 bPtr) 3072 0
        (BitVec.ofNat 256 count) steps st
      let word := loadWord before.memory (bPtr + 32 * steps)
      let loaded := touchMemory before (bPtr + 32 * steps) 32
      let beforeResult := Algorithm.mulBits m acc addend
        (limbBits st.memory bPtr steps)
      have hbefore := ih hsteps'
      dsimp only at hbefore
      have hbeforeReduced := Algorithm.mulBits_lt
        (limbBits st.memory bPtr steps) hmpos haccReduced haddendReduced
      have hloadedAcc : Represents loaded.memory 3072 count beforeResult.1 := by
        simpa only [loaded, YulSemantics.EVM.touchMemory, before,
          beforeResult] using hbefore.1
      have hloadedAddend : Represents loaded.memory 4096 count
          beforeResult.2 := by
        simpa only [loaded, YulSemantics.EVM.touchMemory, before,
          beforeResult] using hbefore.2.1
      have hloadedB : Represents loaded.memory bPtr count bValue := by
        simpa only [loaded, YulSemantics.EVM.touchMemory, before] using
          hbefore.2.2.1
      have hloadedModulus : Represents loaded.memory 0 count m := by
        simpa only [loaded, YulSemantics.EVM.touchMemory, before] using
          hbefore.2.2.2
      have hwordOriginal : word =
          loadWord st.memory (bPtr + 32 * steps) := by
        exact loadWord_eq_of_represents before.memory st.memory bPtr count
          bValue steps hi hbefore.2.2.1 hb
      have hwordProgress := mulBitPrefix_represents loaded word 256 count
        beforeResult.1 beforeResult.2 m (by omega) hcount hmpos hloadedAcc
        hloadedAddend hloadedModulus hbeforeReduced.1 hbeforeReduced.2
      have hwordB := mulBitPrefix_preserves loaded word 256 count bPtr bValue
        (by omega) hcount (by right; omega) (by right; omega)
        (by right; omega) hloadedB
      let afterWord := BigMul.mulBitPrefix 3072 0
        (BitVec.ofNat 256 count) word 256 loaded
      let wordResult := Algorithm.mulBits m beforeResult.1 beforeResult.2
        (wordBits word 256)
      have hbits : limbBits st.memory bPtr (steps + 1) =
          limbBits st.memory bPtr steps ++ wordBits word 256 := by
        rw [limbBits_succ, hwordOriginal]
      have hresult : Algorithm.mulBits m acc addend
          (limbBits st.memory bPtr (steps + 1)) = wordResult := by
        rw [hbits, Algorithm.mulBits_append]
      have hn : (BitVec.ofNat 256 count).toNat = count := by
        rw [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (hcount.trans_lt (by norm_num : 32 < 2 ^ 256))]
      have haddr :
          (wordOffset (BitVec.ofNat 256 bPtr) steps).toNat =
            bPtr + 32 * steps := by
        simp [wordOffset, BitVec.toNat_add, BitVec.toNat_mul,
          Nat.mul_comm steps 32]
        omega
      have hstate : BigMul.mulLimbStep (BitVec.ofNat 256 bPtr) 3072 0
          (BitVec.ofNat 256 count) steps before = afterWord := by
        simp only [BigMul.mulLimbStep, haddr, hn]
        rfl
      have hwordProgress' :
          Represents afterWord.memory 3072 count wordResult.1 ∧
            Represents afterWord.memory 4096 count wordResult.2 ∧
            Represents afterWord.memory 0 count m := by
        simpa only [afterWord, wordResult] using hwordProgress
      have hwordB' : Represents afterWord.memory bPtr count bValue := by
        simpa only [afterWord] using hwordB
      change Represents
          (BigMul.mulLimbStep (BitVec.ofNat 256 bPtr) 3072 0
            (BitVec.ofNat 256 count) steps before).memory
          3072 count
          (Algorithm.mulBits m acc addend
            (limbBits st.memory bPtr (steps + 1))).1 ∧
        Represents
          (BigMul.mulLimbStep (BitVec.ofNat 256 bPtr) 3072 0
            (BitVec.ofNat 256 count) steps before).memory
          4096 count
          (Algorithm.mulBits m acc addend
            (limbBits st.memory bPtr (steps + 1))).2 ∧
        Represents
          (BigMul.mulLimbStep (BitVec.ofNat 256 bPtr) 3072 0
            (BitVec.ofNat 256 count) steps before).memory
          bPtr count bValue ∧
        Represents
          (BigMul.mulLimbStep (BitVec.ofNat 256 bPtr) 3072 0
            (BitVec.ofNat 256 count) steps before).memory
          0 count m
      rw [hstate, hresult]
      exact ⟨hwordProgress'.1, hwordProgress'.2.1, hwordB',
        hwordProgress'.2.2⟩

theorem mulLimbPrefix_preserves (st : EvmState) (bPtr : U256)
    (count steps ptr value : Nat) (hcount : count ≤ 32)
    (hptrOut : 3072 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 3072)
    (hptrAddend : 4096 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 4096)
    (hptrCandidate : 5120 + 32 * count ≤ ptr ∨
      ptr + 32 * count ≤ 5120)
    (hrep : Represents st.memory ptr count value) :
    Represents
      (BigMul.mulLimbPrefix bPtr 3072 0 (BitVec.ofNat 256 count)
        steps st).memory
      ptr count value := by
  induction steps with
  | zero => simpa [BigMul.mulLimbPrefix] using hrep
  | succ steps ih =>
      let before := BigMul.mulLimbPrefix bPtr 3072 0
        (BitVec.ofNat 256 count) steps st
      let address := wordOffset bPtr steps
      let word := loadWord before.memory address.toNat
      let loaded := touchMemory before address.toNat 32
      have hbefore : Represents before.memory ptr count value := by
        simpa only [before] using ih
      have hloaded : Represents loaded.memory ptr count value := by
        simpa [loaded, YulSemantics.EVM.touchMemory] using hbefore
      have hafter := mulBitPrefix_preserves loaded word 256 count ptr value
        (by omega) hcount hptrOut hptrAddend hptrCandidate hloaded
      have hn : (BitVec.ofNat 256 count).toNat = count := by
        rw [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (hcount.trans_lt (by norm_num : 32 < 2 ^ 256))]
      change Represents
        (BigMul.mulLimbStep bPtr 3072 0 (BitVec.ofNat 256 count)
          steps before).memory ptr count value
      simpa only [BigMul.mulLimbStep, hn, address, word, loaded] using hafter

/-- Mathematical state contract for the fixed-memory `mulModBig` calls used
by `modexpBig`.  The multiplier may alias the multiplicand at `0x0800`
(squaring) or occupy the preceding `0x0400` region. -/
theorem mulModBigState_represents (st : EvmState)
    (bPtr count aValue bValue m : Nat) (hcount : count ≤ 32)
    (hbPtr : bPtr + 32 * count ≤ 3072) (hmpos : 0 < m)
    (ha : Represents st.memory 2048 count aValue)
    (hb : Represents st.memory bPtr count bValue)
    (hmodulus : Represents st.memory 0 count m)
    (haReduced : aValue < m) :
    let after := BigMul.mulModBigState st 2048 (BitVec.ofNat 256 bPtr)
      3072 0 (BitVec.ofNat 256 count)
    Represents after.memory 3072 count ((aValue * bValue) % m) ∧
      Represents after.memory 2048 count aValue ∧
      Represents after.memory bPtr count bValue ∧
      Represents after.memory 0 count m := by
  let cleared := clearWordsState st 3072 count
  let copied := copyWordsState cleared 4096 2048 count
  have hclearedOut : Represents cleared.memory 3072 count 0 := by
    exact clearWordsState_represents_zero st 3072 count (by omega)
  have hclearedA : Represents cleared.memory 2048 count aValue := by
    exact clearWordsState_preserves st 3072 2048 count aValue (by omega)
      (by right; omega) ha
  have hclearedB : Represents cleared.memory bPtr count bValue := by
    exact clearWordsState_preserves st 3072 bPtr count bValue (by omega)
      (by right; omega) hb
  have hclearedModulus : Represents cleared.memory 0 count m := by
    exact clearWordsState_preserves st 3072 0 count m (by omega)
      (by right; omega) hmodulus
  have hcopiedOut : Represents copied.memory 3072 count 0 := by
    exact copyWordsState_preserves cleared 4096 2048 3072 count 0
      (by omega) (by right; omega) hclearedOut
  have hcopiedAddend : Represents copied.memory 4096 count aValue := by
    exact copyWordsState_represents cleared 4096 2048 count aValue
      (by omega) (by omega) (by right; omega) hclearedA
  have hcopiedA : Represents copied.memory 2048 count aValue := by
    exact copyWordsState_preserves cleared 4096 2048 2048 count aValue
      (by omega) (by right; omega) hclearedA
  have hcopiedB : Represents copied.memory bPtr count bValue := by
    exact copyWordsState_preserves cleared 4096 2048 bPtr count bValue
      (by omega) (by right; omega) hclearedB
  have hcopiedModulus : Represents copied.memory 0 count m := by
    exact copyWordsState_preserves cleared 4096 2048 0 count m
      (by omega) (by right; omega) hclearedModulus
  let progress := BigMul.mulLimbPrefix (BitVec.ofNat 256 bPtr) 3072 0
    (BitVec.ofNat 256 count) count copied
  let result := Algorithm.mulBits m 0 aValue
    (limbBits copied.memory bPtr count)
  have hprogress := mulLimbPrefix_represents copied bPtr count count 0
    aValue bValue m (by omega) hcount hbPtr hmpos hcopiedOut
    hcopiedAddend hcopiedB hcopiedModulus (by omega) haReduced
  have hprogressA := mulLimbPrefix_preserves copied
    (BitVec.ofNat 256 bPtr) count count 2048 aValue hcount
    (by right; omega) (by right; omega) (by right; omega) hcopiedA
  have hresultLt := Algorithm.mulBits_lt (modulus := m) (acc := 0)
    (addend := aValue) (limbBits copied.memory bPtr count) hmpos
    (by omega) haReduced
  have hvalue := Algorithm.mulBits_fst m 0 aValue
    (limbBits copied.memory bPtr count)
  rw [Nat.mod_eq_of_lt hresultLt.1, value_limbBits,
    value_of_represents hcopiedB] at hvalue
  have hprogress' :
      Represents progress.memory 3072 count result.1 ∧
        Represents progress.memory 4096 count result.2 ∧
        Represents progress.memory bPtr count bValue ∧
        Represents progress.memory 0 count m := by
    simpa only [progress, result] using hprogress
  have hn : (BitVec.ofNat 256 count).toNat = count := by
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hcount.trans_lt (by norm_num : 32 < 2 ^ 256))]
  have hstate : BigMul.mulModBigState st 2048 (BitVec.ofNat 256 bPtr)
      3072 0 (BitVec.ofNat 256 count) = progress := by
    simp only [BigMul.mulModBigState, hn]
    rfl
  change Represents
      (BigMul.mulModBigState st 2048 (BitVec.ofNat 256 bPtr) 3072 0
        (BitVec.ofNat 256 count)).memory
      3072 count ((aValue * bValue) % m) ∧
    Represents
      (BigMul.mulModBigState st 2048 (BitVec.ofNat 256 bPtr) 3072 0
        (BitVec.ofNat 256 count)).memory
      2048 count aValue ∧
    Represents
      (BigMul.mulModBigState st 2048 (BitVec.ofNat 256 bPtr) 3072 0
        (BitVec.ofNat 256 count)).memory
      bPtr count bValue ∧
    Represents
      (BigMul.mulModBigState st 2048 (BitVec.ofNat 256 bPtr) 3072 0
        (BitVec.ofNat 256 count)).memory
      0 count m
  rw [hstate]
  have hresultValue : result.1 = (aValue * bValue) % m := by
    simpa only [result, Nat.zero_add] using hvalue
  rw [← hresultValue]
  exact ⟨hprogress'.1, hprogressA, hprogress'.2.2.1,
    hprogress'.2.2.2⟩

end Challenge.Modexp.Reference.Proofs.Yul.BigMath
