import Challenge.Modexp.Reference.Proofs.Yul.BigMath
import Challenge.Modexp.Reference.Proofs.Yul.BigPath
import Challenge.Modexp.Reference.Proofs.Yul.WordMath
import Challenge.YulProof.NatDigits
import Mathlib.Data.Nat.Bitwise

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

/-!
# Mathematical setup invariants for the direct MODEXP big path

The execution-level setup is proved in `BigPath`; this file interprets its
freshly cleared and loaded memory as arbitrary-precision natural numbers.
No compiled-bytecode proof is imported.
-/

namespace Challenge.Modexp.Reference.Proofs.Yul.BigSetup

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM
open Challenge.YulProof.EvmState
open BigMath

theorem limbCount_toNat (m : Nat) (hm : m ≤ 1024) :
    (BigPath.limbCount (BitVec.ofNat 256 m)).toNat = Limbs.limbCount m := by
  unfold BigPath.limbCount Limbs.limbCount
  rw [BitVec.toNat_udiv, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : m < 2 ^ 256)]
  change ((m + 31) % 2 ^ 256) / 32 = (m + 31) / 32
  rw [Nat.mod_eq_of_lt (by omega : m + 31 < 2 ^ 256)]

theorem clearedOutput_represents_zero (st : EvmState) (m : Nat)
    (hm : m ≤ 1024) :
    Represents
      (BigPath.clearedOutputState st (BitVec.ofNat 256 m)).memory 0
      (Limbs.limbCount m) 0 := by
  let count := Limbs.limbCount m
  have hcount : count ≤ 32 := Limbs.limbCount_le_32 m hm
  have hn := limbCount_toNat m hm
  have h0 : Represents
      (BigPath.clearedModulusState st (BitVec.ofNat 256 m)).memory 0 count 0 := by
    simpa [BigPath.clearedModulusState, hn] using
      clearWordsState_represents_zero st 0 count (by omega)
  have h1 : Represents
      (BigPath.clearedBaseState st (BitVec.ofNat 256 m)).memory 0 count 0 := by
    simpa [BigPath.clearedBaseState, hn] using
      clearWordsState_preserves
        (BigPath.clearedModulusState st (BitVec.ofNat 256 m)) 1024 0 count 0
        (by omega) (Or.inr (by omega)) h0
  have h2 : Represents
      (BigPath.clearedAccumulatorState st (BitVec.ofNat 256 m)).memory 0 count 0 := by
    simpa [BigPath.clearedAccumulatorState, hn] using
      clearWordsState_preserves
        (BigPath.clearedBaseState st (BitVec.ofNat 256 m)) 2048 0 count 0
        (by omega) (Or.inr (by omega)) h1
  simpa [BigPath.clearedOutputState, hn] using
    clearWordsState_preserves
      (BigPath.clearedAccumulatorState st (BitVec.ofNat 256 m)) 6144 0 count 0
      (by omega) (Or.inr (by omega)) h2

/-! ## Big-endian loading into little-endian limbs -/

def partialValue (input : ByteArray) (offset length i : Nat) : Nat :=
  Precompile.bytesToNatPadded input offset i * 256 ^ (length - i)

private theorem partialValue_lt (input : ByteArray)
    (offset length i : Nat) (hi : i ≤ length) :
    partialValue input offset length i <
      Limbs.radix ^ Limbs.limbCount length := by
  have hprefix := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow
    input offset i
  have htail : 0 < 256 ^ (length - i) := Nat.pow_pos (by omega)
  have hpartial : partialValue input offset length i < 256 ^ length := by
    unfold partialValue
    calc
      Precompile.bytesToNatPadded input offset i * 256 ^ (length - i) <
          256 ^ i * 256 ^ (length - i) :=
        Nat.mul_lt_mul_of_pos_right hprefix htail
      _ = 256 ^ length := by rw [← Nat.pow_add]; congr 2; omega
  rw [Limbs.pow_radix]
  exact hpartial.trans_le (Nat.pow_le_pow_right (by omega)
    (Limbs.width_le_limbs length))

theorem loadLimbAddress_toNat (length dst i : Nat)
    (hlength : length < 2 ^ 256) (hi : i < length)
    (hfit : dst + 32 * Limbs.limbCount length < 2 ^ 256) :
    (loadLimbAddress (BitVec.ofNat 256 length)
      (BitVec.ofNat 256 dst) i).toNat =
      dst + 32 * ((length - 1 - i) / 32) := by
  have hlen : (BitVec.ofNat 256 length).toNat = length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlength]
  have hi256 : i < 2 ^ 256 := hi.trans hlength
  have hirev :
      (BitVec.ofNat 256 length - 1 - BitVec.ofNat 256 i).toNat =
        length - 1 - i := by
    rw [BitVec.toNat_sub_of_le, BitVec.toNat_sub_of_le]
    · rw [hlen, show (1 : U256).toNat = 1 by rfl,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi256]
    · simp [BitVec.le_def, hlen]
      omega
    · simp [BitVec.le_def, hlen, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hi256]
      omega
  unfold loadLimbAddress
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_udiv, hirev,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : dst < 2 ^ 256)]
  rw [show (32 : U256).toNat = 32 by rfl]
  have hlimb : (length - 1 - i) / 32 < Limbs.limbCount length := by
    unfold Limbs.limbCount
    omega
  rw [Nat.mod_eq_of_lt (by omega : (length - 1 - i) / 32 * 32 < 2 ^ 256),
    Nat.mod_eq_of_lt (by omega : dst + (length - 1 - i) / 32 * 32 < 2 ^ 256)]
  omega

theorem loadByteShift_eq (length i : Nat) (hlength : length < 2 ^ 256)
    (hi : i < length) :
    loadByteShift (BitVec.ofNat 256 length) i =
      ((length - 1 - i) % 32) * 8 := by
  have hlen : (BitVec.ofNat 256 length).toNat = length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlength]
  have hi256 : i < 2 ^ 256 := hi.trans hlength
  have hirev :
      (BitVec.ofNat 256 length - 1 - BitVec.ofNat 256 i).toNat =
        length - 1 - i := by
    rw [BitVec.toNat_sub_of_le, BitVec.toNat_sub_of_le]
    · rw [hlen, show (1 : U256).toNat = 1 by rfl,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi256]
    · simp [BitVec.le_def, hlen]
      omega
    · simp [BitVec.le_def, hlen, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hi256]
      omega
  unfold loadByteShift
  rw [BitVec.toNat_mul, BitVec.toNat_umod, hirev]
  change (((length - 1 - i) % 32 * 8) % 2 ^ 256) = _
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem lor_eq_add_of_land_eq_zero {a b : Nat}
    (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (hand : a &&& b = 0) :
    a ||| b = a + b := by
  let x : BitVec 256 := BitVec.ofFin ⟨a, ha⟩
  let y : BitVec 256 := BitVec.ofFin ⟨b, hb⟩
  have hx : x.toNat = a := by simp [x]
  have hy : y.toNat = b := by simp [y]
  have hxy : x &&& y = 0#256 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, hx, hy, hand]
    rfl
  calc
    a ||| b = (x ||| y).toNat := by rw [BitVec.toNat_or, hx, hy]
    _ = (x + y).toNat := by rw [BitVec.add_eq_or_of_and_eq_zero x y hxy]
    _ = a + b := by simpa [hx, hy] using BitVec.toNat_add_of_and_eq_zero hxy

private theorem land_separated_blocks (high low shift : Nat)
    (hlow : low < 256) :
    (high * 2 ^ (shift + 8)) &&& (low * 2 ^ shift) = 0 := by
  apply Nat.zero_of_testBit_eq_false
  intro bit
  rw [Nat.testBit_land, Nat.testBit_mul_two_pow,
    Nat.testBit_mul_two_pow]
  by_cases hhigh : shift + 8 ≤ bit
  · have hindex : 8 ≤ bit - shift := by omega
    have hlow' : low < 2 ^ 8 := by norm_num; exact hlow
    have hpow : low < 2 ^ (bit - shift) := by
      exact hlow'.trans_le (Nat.pow_le_pow_right (by omega) hindex)
    rw [Nat.testBit_eq_false_of_lt hpow]
    simp
  · simp [hhigh]

private theorem ofDigits_set_add (radix : Nat) (digits : List Nat)
    (index delta : Nat) (hindex : index < digits.length) :
    Nat.ofDigits radix (digits.set index (digits[index] + delta)) =
      Nat.ofDigits radix digits + delta * radix ^ index := by
  induction digits generalizing index with
  | nil => simp at hindex
  | cons head tail ih =>
      cases index with
      | zero =>
          change Nat.ofDigits radix ((head + delta) :: tail) = _
          simp only [Nat.ofDigits_cons, Nat.pow_zero, Nat.mul_one]
          omega
      | succ index =>
          simp only [List.length_cons, Nat.add_lt_add_iff_right] at hindex
          simp only [List.set_cons_succ, List.getElem_cons_succ,
            Nat.ofDigits_cons]
          rw [ih index hindex, Nat.pow_succ]
          ring

theorem memoryLimbs_store_at (st : EvmState) (ptr count index : Nat)
    (value : U256) (hindex : index < count)
    (hfit : ptr + 32 * count < 2 ^ 256) :
    memoryLimbs
        (storeWordAt st (BitVec.ofNat 256 (ptr + 32 * index)) value).memory
        ptr count =
      (memoryLimbs st.memory ptr count).set index value.toNat := by
  apply List.ext_get
  · simp [memoryLimbs]
  · intro j hjLeft hjRight
    have hj : j < count := by simpa [memoryLimbs] using hjLeft
    have haddr : (BitVec.ofNat 256 (ptr + 32 * index)).toNat =
        ptr + 32 * index := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    by_cases heq : j = index
    · subst j
      simpa [memoryLimbs, hindex, haddr] using
        congrArg BitVec.toNat
          (loadWord_storeWordAt st (BitVec.ofNat 256 (ptr + 32 * index)) value)
    · have hload :
          loadWord
              (storeWordAt st (BitVec.ofNat 256 (ptr + 32 * index)) value).memory
              (ptr + 32 * j) = loadWord st.memory (ptr + 32 * j) := by
        unfold storeWordAt
        rw [YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
        rw [haddr]
        rcases Nat.lt_or_gt_of_ne heq with hbefore | hafter
        · right; omega
        · left; omega
      simp only [memoryLimbs, List.get_eq_getElem, List.getElem_map,
        List.getElem_range]
      rw [List.getElem_set (by simpa using hj)]
      simp only [if_neg (Ne.symm heq)]
      have hmap : j <
          (List.map (fun i => (loadWord st.memory (ptr + 32 * i)).toNat)
            (List.range count)).length := by simpa using hj
      have hrhs :
          (List.map (fun i => (loadWord st.memory (ptr + 32 * i)).toNat)
            (List.range count))[j]'hmap =
            (loadWord st.memory (ptr + 32 * j)).toNat := by simp
      rw [hrhs]
      exact congrArg BitVec.toNat hload

@[simp] theorem loadBigEndianPrefix_env (st : EvmState)
    (off len dst : U256) (i : Nat) :
    (loadBigEndianPrefix st off len dst i).env = st.env := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simpa [loadBigEndianPrefix, loadBigEndianStep,
        YulSemantics.EVM.touchMemory] using ih

theorem value_memoryLimbs_store_add (st : EvmState)
    (ptr count index delta : Nat) (hindex : index < count)
    (hfit : ptr + 32 * count < 2 ^ 256)
    (haddFit : (loadWord st.memory (ptr + 32 * index)).toNat + delta <
      2 ^ 256) :
    Nat.ofDigits Limbs.radix
        (memoryLimbs
          (storeWordAt st (BitVec.ofNat 256 (ptr + 32 * index))
            (BitVec.ofNat 256
              ((loadWord st.memory (ptr + 32 * index)).toNat + delta))).memory
          ptr count) =
      Nat.ofDigits Limbs.radix (memoryLimbs st.memory ptr count) +
        delta * Limbs.radix ^ index := by
  let value := BitVec.ofNat 256
    ((loadWord st.memory (ptr + 32 * index)).toNat + delta)
  have hvalue : value.toNat =
      (loadWord st.memory (ptr + 32 * index)).toNat + delta := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddFit]
  rw [show BitVec.ofNat 256
      ((loadWord st.memory (ptr + 32 * index)).toNat + delta) = value by rfl,
    memoryLimbs_store_at st ptr count index value hindex hfit, hvalue]
  have hidxlen : index < (memoryLimbs st.memory ptr count).length := by
    simpa using hindex
  have hget : (memoryLimbs st.memory ptr count)[index]'hidxlen =
      (loadWord st.memory (ptr + 32 * index)).toNat := by
    simp [memoryLimbs]
  rw [← hget]
  exact ofDigits_set_add Limbs.radix (memoryLimbs st.memory ptr count)
    index delta (by simpa using hindex)

private theorem partial_digit (headValue index rem : Nat) (hrem : rem < 32) :
    (headValue * 256 ^ (32 * index + (rem + 1)) /
          Limbs.radix ^ index) % Limbs.radix =
      (headValue % 256 ^ (31 - rem)) * 256 ^ (rem + 1) := by
  have hsplit : 31 - rem + (rem + 1) = 32 := by omega
  rw [Limbs.radix_eq, ← Nat.pow_mul, Nat.pow_add]
  have hpow : 0 < 256 ^ (32 * index) := Nat.pow_pos (by omega)
  rw [show headValue * (256 ^ (32 * index) * 256 ^ (rem + 1)) =
      256 ^ (32 * index) * (headValue * 256 ^ (rem + 1)) by ring]
  rw [Nat.mul_div_cancel_left _ hpow, ← hsplit,
    Nat.pow_add 256 (31 - rem) (rem + 1)]
  exact Nat.mul_mod_mul_right (256 ^ (rem + 1)) headValue
    (256 ^ (31 - rem))

private theorem loaded_digit_factor (input : ByteArray)
    (offset length i : Nat) (hi : i < length) :
    partialValue input offset length i /
          Limbs.radix ^ ((length - 1 - i) / 32) % Limbs.radix =
      (Precompile.bytesToNatPadded input offset i %
          256 ^ (31 - (length - 1 - i) % 32)) *
        256 ^ ((length - 1 - i) % 32 + 1) := by
  let reverse := length - 1 - i
  have hrem : reverse % 32 < 32 := Nat.mod_lt _ (by omega)
  have hrecompose :
      32 * (reverse / 32) + (reverse % 32 + 1) = length - i := by
    have hdiv := Nat.div_add_mod reverse 32
    dsimp only [reverse]
    omega
  unfold partialValue
  rw [← hrecompose]
  exact partial_digit _ _ _ hrem

private theorem partialValue_succ (input : ByteArray)
    (offset length i : Nat) (hi : i < length) :
    partialValue input offset length i +
        (byteFrom input.toList (offset + i)).toNat *
          256 ^ ((length - 1 - i) % 32) *
          Limbs.radix ^ ((length - 1 - i) / 32) =
      partialValue input offset length (i + 1) := by
  let reverse := length - 1 - i
  let limb := reverse / 32
  let rem := reverse % 32
  have hrecompose : 32 * limb + rem = reverse := by
    dsimp only [limb, rem]
    simpa [Nat.mul_comm] using Nat.div_add_mod reverse 32
  have htail : length - i = reverse + 1 := by
    dsimp only [reverse]
    omega
  have htailNext : length - (i + 1) = reverse := by
    dsimp only [reverse]
    omega
  unfold partialValue
  rw [Challenge.EvmProof.Bytes.bytesToNatPadded_succ, htail, htailNext,
    Limbs.radix_eq, ← Nat.pow_mul, ← hrecompose, Nat.pow_succ,
    Nat.pow_add 256 (32 * limb) rem]
  ring

theorem loadBigEndianPrefix_represents_partial (st : EvmState)
    (input : ByteArray) (offset dst length i : Nat)
    (hcalldata : st.env.calldata = input.toList)
    (hlength : length < 2 ^ 256) (hoffset : offset + length < 2 ^ 256)
    (hi : i ≤ length)
    (hfit : dst + 32 * Limbs.limbCount length < 2 ^ 256)
    (hzero : Represents st.memory dst (Limbs.limbCount length) 0) :
    Represents
      (loadBigEndianPrefix st (BitVec.ofNat 256 offset)
        (BitVec.ofNat 256 length) (BitVec.ofNat 256 dst) i).memory
      dst (Limbs.limbCount length) (partialValue input offset length i) := by
  induction i with
  | zero => simpa [loadBigEndianPrefix, partialValue] using hzero
  | succ i ih =>
      have hiStep : i < length := by omega
      have hbefore := ih (by omega)
      let before := loadBigEndianPrefix st (BitVec.ofNat 256 offset)
        (BitVec.ofNat 256 length) (BitVec.ofNat 256 dst) i
      let reverse := length - 1 - i
      let limb := reverse / 32
      let rem := reverse % 32
      let byte := (byteFrom input.toList (offset + i)).toNat
      let delta := byte * 256 ^ rem
      let high := Precompile.bytesToNatPadded input offset i % 256 ^ (31 - rem)
      have hlimb : limb < Limbs.limbCount length := by
        dsimp only [limb, reverse]
        unfold Limbs.limbCount
        omega
      have haddr := loadLimbAddress_toNat length dst i hlength hiStep hfit
      have hshift := loadByteShift_eq length i hlength hiStep
      have hidx : limb < (memoryLimbs before.memory dst
          (Limbs.limbCount length)).length := by simpa using hlimb
      have hdidx : limb < (Limbs.limbDigits (Limbs.limbCount length)
          (partialValue input offset length i)).length := by
        rw [Limbs.length_limbDigits (partialValue_lt input offset length i
          (by omega))]
        exact hlimb
      have hloaded :
          (loadWord before.memory (dst + 32 * limb)).toNat =
            high * 256 ^ (rem + 1) := by
        calc
          (loadWord before.memory (dst + 32 * limb)).toNat =
              (memoryLimbs before.memory dst
                (Limbs.limbCount length))[limb]'hidx := by
            simp [memoryLimbs]
          _ = (Limbs.limbDigits (Limbs.limbCount length)
                (partialValue input offset length i))[limb]'hdidx := by
            have hbeforeDigits : memoryLimbs before.memory dst
                (Limbs.limbCount length) =
                Limbs.limbDigits (Limbs.limbCount length)
                  (partialValue input offset length i) := by
              simpa [Limbs.limbDigits, Limbs.radix,
                Challenge.YulProof.Limbs.limbDigits,
                Challenge.YulProof.Limbs.radix] using hbefore.2
            have hopt := congrArg (fun xs : List Nat => xs[limb]?)
              hbeforeDigits
            rw [List.getElem?_eq_getElem hidx,
              List.getElem?_eq_getElem hdidx] at hopt
            exact Option.some.inj hopt
          _ = partialValue input offset length i / Limbs.radix ^ limb %
                Limbs.radix := by
            have hdigit := Challenge.YulProof.NatDigits.getElem_eq_div_mod_ofDigits
              Limbs.radix
              (Limbs.limbDigits (Limbs.limbCount length)
                (partialValue input offset length i)) limb Limbs.radix_pos
              (by rw [Limbs.length_limbDigits
                    (partialValue_lt input offset length i (by omega))]
                  exact hlimb)
              (fun digit hdigit => Limbs.limbDigits_lt hdigit)
            rw [Limbs.value_limbDigits] at hdigit
            exact hdigit
          _ = high * 256 ^ (rem + 1) := by
            simpa [limb, rem, reverse, high] using
              loaded_digit_factor input offset length i hiStep
      have hbyte : byte < 256 := by
        exact (byteFrom input.toList (offset + i)).toNat_lt
      have hp : 256 ^ (rem + 1) = 2 ^ (8 * rem + 8) := by
        calc
          256 ^ (rem + 1) = (2 ^ 8) ^ (rem + 1) := by norm_num
          _ = 2 ^ (8 * (rem + 1)) := (Nat.pow_mul 2 8 _).symm
          _ = 2 ^ (8 * rem + 8) := by ring
      have hq : 256 ^ rem = 2 ^ (8 * rem) := by
        calc
          256 ^ rem = (2 ^ 8) ^ rem := by norm_num
          _ = 2 ^ (8 * rem) := (Nat.pow_mul 2 8 _).symm
      have hland : (high * 256 ^ (rem + 1)) &&& delta = 0 := by
        simpa [delta, hp, hq] using
          land_separated_blocks high byte (8 * rem) hbyte
      have hoff : (BitVec.ofNat 256 offset).toNat = offset := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2 ^ 256)]
      have hsourceByte :
          (StateModel.calldataByteValue before
            (BitVec.ofNat 256 offset + BitVec.ofNat 256 i)).toNat = byte := by
        have henv : before.env = st.env := by
          exact loadBigEndianPrefix_env st _ _ _ i
        have hcalldata' : before.env.calldata = input.toList := by
          rw [henv, hcalldata]
        have hoffsum :
            (BitVec.ofNat 256 offset + BitVec.ofNat 256 i).toNat = offset + i := by
          have hiword : (BitVec.ofNat 256 i).toNat = i := by
            rw [BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : i < 2 ^ 256)]
          rw [BitVec.toNat_add, hoff, hiword]
          rw [Nat.mod_eq_of_lt (by omega : offset + i < 2 ^ 256)]
        rw [WordMath.calldataByteValue_toNat before input _ hcalldata',
          hoffsum]
      let shifted :=
        StateModel.calldataByteValue before
          (BitVec.ofNat 256 offset + BitVec.ofNat 256 i) <<< (8 * rem)
      have hshifted : shifted.toNat = delta := by
        simp only [shifted, BitVec.toNat_shiftLeft, hsourceByte]
        rw [Nat.shiftLeft_eq]
        rw [Nat.mod_eq_of_lt]
        · rw [← hq]
        · have hbpow : byte < 2 ^ 8 := by omega
          calc
            byte * 2 ^ (8 * rem) < 2 ^ 8 * 2 ^ (8 * rem) :=
              Nat.mul_lt_mul_of_pos_right hbpow (Nat.pow_pos (by omega))
            _ = 2 ^ (8 + 8 * rem) := by rw [← Nat.pow_add]
            _ ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) (by
              dsimp [rem]
              have := Nat.mod_lt reverse (by omega : 0 < 32)
              omega)
      have hlor :
          (loadWord before.memory (dst + 32 * limb) ||| shifted).toNat =
            (loadWord before.memory (dst + 32 * limb)).toNat + delta := by
        rw [BitVec.toNat_or, hshifted, hloaded]
        exact lor_eq_add_of_land_eq_zero
          (by rw [← hloaded]; exact (loadWord before.memory _).isLt)
          (by rw [← hshifted]; exact shifted.isLt) hland
      have haddFit :
          (loadWord before.memory (dst + 32 * limb)).toNat + delta <
            2 ^ 256 := by
        rw [← hlor]
        exact (loadWord before.memory (dst + 32 * limb) ||| shifted).isLt
      have hvalueWord :
          loadWord before.memory (dst + 32 * limb) ||| shifted =
            BitVec.ofNat 256
              ((loadWord before.memory (dst + 32 * limb)).toNat + delta) := by
        apply BitVec.eq_of_toNat_eq
        rw [hlor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddFit]
      have hwrite := value_memoryLimbs_store_add before dst
        (Limbs.limbCount length) limb delta hlimb hfit haddFit
      rw [value_of_represents hbefore] at hwrite
      apply (represents_iff_value
        (partialValue_lt input offset length (i + 1) hi)).2
      rw [← partialValue_succ input offset length i hiStep, ← hwrite]
      have hstepMemory :
          (loadBigEndianStep before (BitVec.ofNat 256 offset)
            (BitVec.ofNat 256 length) (BitVec.ofNat 256 dst) i).memory =
            (storeWordAt before (BitVec.ofNat 256 (dst + 32 * limb))
              (BitVec.ofNat 256
                ((loadWord before.memory (dst + 32 * limb)).toNat + delta))).memory := by
        simp only [loadBigEndianStep, storeWordAt,
          YulSemantics.EVM.touchMemory]
        rw [haddr, hshift]
        have hlimbDef : (length - 1 - i) / 32 = limb := rfl
        have hremDef : (length - 1 - i) % 32 = rem := rfl
        rw [hlimbDef, hremDef]
        have hrawShift :
            ((wordFrom before.env.calldata
                (BitVec.ofNat 256 offset + BitVec.ofNat 256 i).toNat >>> 248) &&&
              0xff) <<< (rem * 8) = shifted := by
          simp [shifted, StateModel.calldataByteValue, Nat.mul_comm]
        rw [hrawShift]
        have hdstAddr : (BitVec.ofNat 256 (dst + 32 * limb)).toNat =
            dst + 32 * limb := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [hdstAddr, hvalueWord]
      change Nat.ofDigits Limbs.radix
        (memoryLimbs
          (loadBigEndianStep before (BitVec.ofNat 256 offset)
            (BitVec.ofNat 256 length) (BitVec.ofNat 256 dst) i).memory
          dst (Limbs.limbCount length)) = _
      rw [hstepMemory]

theorem loadBigEndianPrefix_represents (st : EvmState) (input : ByteArray)
    (offset dst length : Nat) (hcalldata : st.env.calldata = input.toList)
    (hlength : length < 2 ^ 256) (hoffset : offset + length < 2 ^ 256)
    (hfit : dst + 32 * Limbs.limbCount length < 2 ^ 256)
    (hzero : Represents st.memory dst (Limbs.limbCount length) 0) :
    Represents
      (loadBigEndianPrefix st (BitVec.ofNat 256 offset)
        (BitVec.ofNat 256 length) (BitVec.ofNat 256 dst) length).memory
      dst (Limbs.limbCount length)
        (Precompile.bytesToNatPadded input offset length) := by
  simpa [partialValue] using
    loadBigEndianPrefix_represents_partial st input offset dst length length
      hcalldata hlength hoffset (by omega) hfit hzero

/-! ## Challenge-level modulus setup -/

def modulusOffset (input : ByteArray) : Nat :=
  96 + baseSize input + exponentSize input

def modulusNat (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input (modulusOffset input) (modulusSize input)

@[simp] theorem clearWordsState_env (st : EvmState) (ptr : U256) (count : Nat) :
    (clearWordsState st ptr count).env = st.env := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa [clearWordsState, storeWordAt, YulSemantics.EVM.touchMemory] using ih

theorem clearedOutput_env (st : EvmState) (modulusSize : U256) :
    (BigPath.clearedOutputState st modulusSize).env = st.env := by
  simp [BigPath.clearedOutputState, BigPath.clearedAccumulatorState,
    BigPath.clearedBaseState, BigPath.clearedModulusState]

/-- The exact source setup loads the padded modulus into the little-endian
limb array at address zero.  Fresh memory is not needed: the source clears the
whole destination before loading. -/
theorem loadedModulus_represents (st : EvmState) (input : ByteArray)
    (hcalldata : st.env.calldata = input.toList) (hvalid : ValidInput input) :
    Represents
      (BigPath.loadedModulusState st (BitVec.ofNat 256 (modulusSize input))
        (BitVec.ofNat 256 (modulusOffset input))).memory
      0 (Limbs.limbCount (modulusSize input)) (modulusNat input) := by
  let m := modulusSize input
  let off := modulusOffset input
  have hm : m ≤ 1024 := hvalid.2.2.2
  have hcount : Limbs.limbCount m ≤ 32 := Limbs.limbCount_le_32 m hm
  have hmSmall : m < 2 ^ 256 := by omega
  have hoffSmall : off + m < 2 ^ 256 := by
    rcases hvalid with ⟨_, hb, he, hm⟩
    dsimp [off, modulusOffset]
    omega
  let cleared := BigPath.clearedOutputState st (BitVec.ofNat 256 m)
  have hzero : Represents cleared.memory 0 (Limbs.limbCount m) 0 :=
    clearedOutput_represents_zero st m hm
  have hclearedCalldata : cleared.env.calldata = input.toList := by
    rw [show cleared.env = st.env by
      exact clearedOutput_env st (BitVec.ofNat 256 m), hcalldata]
  have hload := loadBigEndianPrefix_represents cleared input off 0 m
    hclearedCalldata hmSmall hoffSmall (by omega : 0 + 32 * Limbs.limbCount m <
      2 ^ 256) hzero
  have hmWord : (BitVec.ofNat 256 m).toNat = m := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmSmall]
  simpa [BigPath.loadedModulusState, cleared, m, off, modulusNat, hmWord]
    using hload

@[simp] theorem modulusScanPrefix_memory (count : Nat) (st : EvmState) :
    (modulusScanPrefix count st).memory = st.memory := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa [modulusScanPrefix, YulSemantics.EVM.touchMemory] using ih

private theorem nat_or_eq_zero_iff (x y : Nat) :
    x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · apply Nat.zero_of_testBit_eq_false
      intro bit
      have ht := congrArg (fun n : Nat => n.testBit bit) h
      rw [Nat.testBit_or] at ht
      have hz : Nat.testBit 0 bit = false := by simp
      rw [hz] at ht
      exact (Bool.or_eq_false_iff.mp ht).1
    · apply Nat.zero_of_testBit_eq_false
      intro bit
      have ht := congrArg (fun n : Nat => n.testBit bit) h
      rw [Nat.testBit_or] at ht
      have hz : Nat.testBit 0 bit = false := by simp
      rw [hz] at ht
      exact (Bool.or_eq_false_iff.mp ht).2
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem word_or_eq_zero_iff (x y : U256) :
    x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    rw [BitVec.toNat_or, show (0 : U256).toNat = 0 by rfl] at hn
    have hp := (nat_or_eq_zero_iff _ _).mp hn
    exact ⟨BitVec.eq_of_toNat_eq hp.1, BitVec.eq_of_toNat_eq hp.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem modulusOrPrefix_eq_zero_iff (st : EvmState) (count : Nat)
    (hcount : count ≤ 32) :
    modulusOrPrefix count st = 0 ↔
      memoryLimbs st.memory 0 count = List.replicate count 0 := by
  induction count with
  | zero => simp [modulusOrPrefix, memoryLimbs]
  | succ count ih =>
      have hi : count < 2 ^ 256 := by omega
      have haddr :
          (BitVec.ofNat 256 count * (32 : U256)).toNat = 32 * count := by
        rw [BitVec.toNat_mul, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hi, show (32 : U256).toNat = 32 by rfl,
          Nat.mod_eq_of_lt (by omega : count * 32 < 2 ^ 256)]
        omega
      rw [modulusOrPrefix]
      rw [show (modulusScanPrefix count st).memory = st.memory by
        exact modulusScanPrefix_memory count st]
      rw [haddr]
      rw [memoryLimbs_succ]
      have ih' := ih (by omega)
      constructor
      · intro hor
        have hparts := (word_or_eq_zero_iff _ _).mp hor
        rw [ih'.mp hparts.1]
        have hword : loadWord st.memory (32 * count) = 0 := hparts.2
        simp [hword, List.replicate_succ']
      · intro hl
        rw [List.replicate_succ'] at hl
        have hprefix : memoryLimbs st.memory 0 count = List.replicate count 0 := by
          have := congrArg (List.take count) hl
          simpa using this
        have hword : loadWord st.memory (32 * count) = 0 := by
          have := congrArg (fun xs : List Nat => xs[count]?) hl
          apply BitVec.eq_of_toNat_eq
          simpa using this
        rw [ih'.mpr hprefix, hword]
        simp

/-- The source scan branches on zero exactly when the mathematical padded
modulus is zero. -/
theorem modulusOrValue_eq_zero_iff (st : EvmState) (input : ByteArray)
    (hcalldata : st.env.calldata = input.toList) (hvalid : ValidInput input) :
    BigPath.modulusOrValue st (BitVec.ofNat 256 (modulusSize input))
        (BitVec.ofNat 256 (modulusOffset input)) = 0 ↔
      modulusNat input = 0 := by
  let m := modulusSize input
  let count := Limbs.limbCount m
  have hm : m ≤ 1024 := hvalid.2.2.2
  have hcount : count ≤ 32 := Limbs.limbCount_le_32 m hm
  have hn := limbCount_toNat m hm
  have hrep := loadedModulus_represents st input hcalldata hvalid
  rw [BigPath.modulusOrValue, hn,
    modulusOrPrefix_eq_zero_iff _ count hcount]
  constructor
  · intro hzero
    have hvalue := value_of_represents hrep
    rw [hzero] at hvalue
    simpa using hvalue.symm
  · intro hvalue
    rw [hvalue] at hrep
    simpa [Limbs.limbDigits, Challenge.YulProof.Limbs.limbDigits,
      Nat.digitsAppend] using hrep.2

/-! ## Nonzero scratch prelude -/

theorem storeWordAt_preserves (st : EvmState) (write : U256)
    (ptr count value : Nat) (v : U256)
    (hdisjoint : write.toNat + 32 ≤ ptr ∨ ptr + 32 * count ≤ write.toNat)
    (hrep : Represents st.memory ptr count value) :
    Represents (storeWordAt st write v).memory ptr count value :=
  ⟨hrep.1, (memoryLimbs_store_disjoint st write ptr count v hdisjoint).trans
    hrep.2⟩

/-- Loading one operand preserves any limb region disjoint from its complete
destination array. -/
theorem loadBigEndianPrefix_preserves (st : EvmState) (off len dst : Nat)
    (steps ptr count value : Nat) (hsteps : steps ≤ len)
    (hlen : len < 2 ^ 256)
    (hfit : dst + 32 * Limbs.limbCount len < 2 ^ 256)
    (hdisjoint : dst + 32 * Limbs.limbCount len ≤ ptr ∨
      ptr + 32 * count ≤ dst)
    (hrep : Represents st.memory ptr count value) :
    Represents (loadBigEndianPrefix st (BitVec.ofNat 256 off)
      (BitVec.ofNat 256 len) (BitVec.ofNat 256 dst) steps).memory
      ptr count value := by
  induction steps with
  | zero => exact hrep
  | succ steps ih =>
      have hstep : steps < len := by omega
      let before := loadBigEndianPrefix st (BitVec.ofNat 256 off)
        (BitVec.ofNat 256 len) (BitVec.ofNat 256 dst) steps
      let p := loadLimbAddress (BitVec.ofNat 256 len)
        (BitVec.ofNat 256 dst) steps
      let byte :=
        (wordFrom before.env.calldata
          (BitVec.ofNat 256 off + BitVec.ofNat 256 steps).toNat >>> 248) &&& 0xff
      let v := loadWord before.memory p.toNat |||
        (byte <<< loadByteShift (BitVec.ofNat 256 len) steps)
      have hbefore := ih (by omega)
      have hp := loadLimbAddress_toNat len dst steps hlen hstep hfit
      have hpDisjoint : p.toNat + 32 ≤ ptr ∨ ptr + 32 * count ≤ p.toNat := by
        rw [hp]
        rcases hdisjoint with hafter | hbeforeRegion
        · left
          have hlimb : (len - 1 - steps) / 32 < Limbs.limbCount len := by
            unfold Limbs.limbCount
            omega
          omega
        · right; omega
      have hpreserved := storeWordAt_preserves
        (touchMemory before p.toNat 32) p ptr count value v hpDisjoint
        (by simpa [YulSemantics.EVM.touchMemory] using hbefore)
      simpa [loadBigEndianPrefix, loadBigEndianStep, before, p, byte, v,
        storeWordAt, YulSemantics.EVM.touchMemory] using hpreserved

theorem clearedOutput_base_zero (st : EvmState) (m : Nat) (hm : m ≤ 1024) :
    Represents
      (BigPath.clearedOutputState st (BitVec.ofNat 256 m)).memory 1024
      (Limbs.limbCount m) 0 := by
  let count := Limbs.limbCount m
  have hcount : count ≤ 32 := Limbs.limbCount_le_32 m hm
  have hn := limbCount_toNat m hm
  have hbase : Represents
      (BigPath.clearedBaseState st (BitVec.ofNat 256 m)).memory 1024 count 0 := by
    simpa [BigPath.clearedBaseState, hn] using
      clearWordsState_represents_zero
        (BigPath.clearedModulusState st (BitVec.ofNat 256 m)) 1024 count
        (by omega)
  have hacc : Represents
      (BigPath.clearedAccumulatorState st (BitVec.ofNat 256 m)).memory
      1024 count 0 := by
    simpa [BigPath.clearedAccumulatorState, hn] using
      clearWordsState_preserves
        (BigPath.clearedBaseState st (BitVec.ofNat 256 m)) 2048 1024 count 0
        (by omega) (Or.inr (by omega)) hbase
  simpa [BigPath.clearedOutputState, hn] using
    clearWordsState_preserves
      (BigPath.clearedAccumulatorState st (BitVec.ofNat 256 m)) 6144 1024
      count 0 (by omega) (Or.inr (by omega)) hacc

theorem clearedOutput_accumulator_zero (st : EvmState) (m : Nat)
    (hm : m ≤ 1024) :
    Represents
      (BigPath.clearedOutputState st (BitVec.ofNat 256 m)).memory 2048
      (Limbs.limbCount m) 0 := by
  let count := Limbs.limbCount m
  have hcount : count ≤ 32 := Limbs.limbCount_le_32 m hm
  have hn := limbCount_toNat m hm
  have hacc : Represents
      (BigPath.clearedAccumulatorState st (BitVec.ofNat 256 m)).memory
      2048 count 0 := by
    simpa [BigPath.clearedAccumulatorState, hn] using
      clearWordsState_represents_zero
        (BigPath.clearedBaseState st (BitVec.ofNat 256 m)) 2048 count
        (by omega)
  simpa [BigPath.clearedOutputState, hn] using
    clearWordsState_preserves
      (BigPath.clearedAccumulatorState st (BitVec.ofNat 256 m)) 6144 2048
      count 0 (by omega) (Or.inr (by omega)) hacc

/-- The complete nonzero prelude establishes the four mathematical arrays
used by base conversion: modulus, zero base, zero accumulator, and scratch
one. -/
theorem scratchOneState_invariants (st : EvmState) (input : ByteArray)
    (hcalldata : st.env.calldata = input.toList) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input) :
    let count := Limbs.limbCount (modulusSize input)
    let scratch := BigPath.scratchOneState st
      (BitVec.ofNat 256 (modulusSize input))
      (BitVec.ofNat 256 (modulusOffset input))
    Represents scratch.memory 0 count (modulusNat input) ∧
      Represents scratch.memory 1024 count 0 ∧
      Represents scratch.memory 2048 count 0 ∧
      Represents scratch.memory 3072 count 1 := by
  let m := modulusSize input
  let off := modulusOffset input
  let count := Limbs.limbCount m
  let loaded := BigPath.loadedModulusState st (BitVec.ofNat 256 m)
    (BitVec.ofNat 256 off)
  let scanned := BigPath.scannedModulusState st (BitVec.ofNat 256 m)
    (BitVec.ofNat 256 off)
  let cleared := BigPath.scratchClearedState st (BitVec.ofNat 256 m)
    (BitVec.ofNat 256 off)
  let scratch := BigPath.scratchOneState st (BitVec.ofNat 256 m)
    (BitVec.ofNat 256 off)
  have hm : m ≤ 1024 := hvalid.2.2.2
  have hcount : count ≤ 32 := Limbs.limbCount_le_32 m hm
  have hcountPos : 0 < count := Limbs.limbCount_pos (by dsimp [m]; omega)
  have hn := limbCount_toNat m hm
  have hloadedMod : Represents loaded.memory 0 count (modulusNat input) := by
    simpa [loaded, m, off] using loadedModulus_represents st input hcalldata hvalid
  have hloadedBase : Represents loaded.memory 1024 count 0 := by
    dsimp [loaded, BigPath.loadedModulusState]
    rw [show (BitVec.ofNat 256 m).toNat = m by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : m < 2 ^ 256)]]
    apply loadBigEndianPrefix_preserves
      (BigPath.clearedOutputState st (BitVec.ofNat 256 m))
      off m 0 m 1024 count 0
    · omega
    · omega
    · simpa using (show 32 * count < 2 ^ 256 by omega)
    · left
      simpa using (show 32 * count ≤ 1024 by omega)
    · exact clearedOutput_base_zero st m hm
  have hloadedAcc : Represents loaded.memory 2048 count 0 := by
    dsimp [loaded, BigPath.loadedModulusState]
    rw [show (BitVec.ofNat 256 m).toNat = m by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : m < 2 ^ 256)]]
    apply loadBigEndianPrefix_preserves
      (BigPath.clearedOutputState st (BitVec.ofNat 256 m))
      off m 0 m 2048 count 0
    · omega
    · omega
    · simpa using (show 32 * count < 2 ^ 256 by omega)
    · left
      simpa using (show 32 * count ≤ 2048 by omega)
    · exact clearedOutput_accumulator_zero st m hm
  have hscannedMod : Represents scanned.memory 0 count (modulusNat input) := by
    simpa [scanned, BigPath.scannedModulusState, hn,
      modulusScanPrefix_memory] using hloadedMod
  have hscannedBase : Represents scanned.memory 1024 count 0 := by
    simpa [scanned, BigPath.scannedModulusState, hn,
      modulusScanPrefix_memory] using hloadedBase
  have hscannedAcc : Represents scanned.memory 2048 count 0 := by
    simpa [scanned, BigPath.scannedModulusState, hn,
      modulusScanPrefix_memory] using hloadedAcc
  have hclearedMod : Represents cleared.memory 0 count (modulusNat input) := by
    simpa [cleared, BigPath.scratchClearedState, hn] using
      clearWordsState_preserves scanned 3072 0 count (modulusNat input)
        (by omega) (Or.inr (by omega)) hscannedMod
  have hclearedBase : Represents cleared.memory 1024 count 0 := by
    simpa [cleared, BigPath.scratchClearedState, hn] using
      clearWordsState_preserves scanned 3072 1024 count 0
        (by omega) (Or.inr (by omega)) hscannedBase
  have hclearedAcc : Represents cleared.memory 2048 count 0 := by
    simpa [cleared, BigPath.scratchClearedState, hn] using
      clearWordsState_preserves scanned 3072 2048 count 0
        (by omega) (Or.inr (by omega)) hscannedAcc
  have hclearedScratch : Represents cleared.memory 3072 count 0 := by
    simpa [cleared, BigPath.scratchClearedState, hn] using
      clearWordsState_represents_zero scanned 3072 count (by omega)
  have hloadZero : (loadWord cleared.memory 3072).toNat = 0 := by
    have hget := congrArg (fun xs : List Nat => xs[0]?) hclearedScratch.2
    simpa [memoryLimbs, hcountPos, Limbs.limbDigits,
      Challenge.YulProof.Limbs.limbDigits, Nat.digitsAppend] using hget
  have hscratchValue := value_memoryLimbs_store_add cleared 3072 count 0 1
    hcountPos (by omega) (by rw [hloadZero]; omega)
  rw [value_of_represents hclearedScratch, hloadZero] at hscratchValue
  have hscratchOne : Represents scratch.memory 3072 count 1 := by
    apply (represents_iff_value
      (Nat.one_lt_pow hcountPos.ne' Limbs.radix_gt_one)).2
    simpa [scratch, BigPath.scratchOneState, cleared] using hscratchValue
  have hscratchMod : Represents scratch.memory 0 count (modulusNat input) := by
    simpa [scratch, BigPath.scratchOneState, cleared] using
      storeWordAt_preserves cleared 3072 0 count (modulusNat input) 1
        (Or.inr (by change 0 + 32 * count ≤ 3072; omega)) hclearedMod
  have hscratchBase : Represents scratch.memory 1024 count 0 := by
    simpa [scratch, BigPath.scratchOneState, cleared] using
      storeWordAt_preserves cleared 3072 1024 count 0 1
        (Or.inr (by change 1024 + 32 * count ≤ 3072; omega)) hclearedBase
  have hscratchAcc : Represents scratch.memory 2048 count 0 := by
    simpa [scratch, BigPath.scratchOneState, cleared] using
      storeWordAt_preserves cleared 3072 2048 count 0 1
        (Or.inr (by change 2048 + 32 * count ≤ 3072; omega)) hclearedAcc
  exact ⟨hscratchMod, hscratchBase, hscratchAcc, hscratchOne⟩

end Challenge.Modexp.Reference.Proofs.Yul.BigSetup
