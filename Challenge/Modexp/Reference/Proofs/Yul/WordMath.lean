import Challenge.Modexp.Reference.Proofs.Yul.StateModel
import Challenge.Modexp.Reference.Proofs.Algorithm
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Memory
import Mathlib.Tactic.Ring

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Mathematical bridge for the source MODEXP word path

This module relates the exact `BitVec 256` loop states used by the direct Yul
proof to the byte-oriented precompile specification.  Nothing here depends on
the source interpreter's execution judgments.
-/

namespace Challenge.Modexp.Reference.Proofs.Yul.WordMath

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM
open YulEvmCompiler
open StateModel

theorem wordFrom_toNat (input : ByteArray) (offset : Nat) :
    (wordFrom input.toList offset).toNat =
      Precompile.bytesToNatPadded input offset 32 := by
  have hload := (Challenge.EvmProof.Bytes.memMatch_toList input).loadWord offset
  change conv (wordFrom input.toList offset) = MachineState.readWord input offset at hload
  have hnat := congrArg UInt256.toNat hload
  simpa [Challenge.EvmProof.Bytes.readWord_toNat] using hnat

theorem calldataByteValue_toNat (st : EvmState) (input : ByteArray) (off : U256)
    (hcalldata : st.env.calldata = input.toList) :
    (calldataByteValue st off).toNat =
      (byteFrom input.toList off.toNat).toNat := by
  have hshift := Challenge.EvmProof.Bytes.readWord_shift_toNat input off.toNat 1
    (by omega)
  rw [Challenge.EvmProof.Bytes.readWord_toNat] at hshift
  norm_num at hshift
  have hone := Challenge.EvmProof.Bytes.bytesToNatPadded_succ input off.toNat 0
  have hbyte : Precompile.bytesToNatPadded input off.toNat 1 =
      (byteFrom input.toList off.toNat).toNat := by simpa using hone
  unfold calldataByteValue
  rw [hcalldata, BitVec.toNat_and, BitVec.toNat_ushiftRight, wordFrom_toNat,
    show ((0xff : U256)).toNat = 0xff by rfl, hshift, hbyte]
  rw [show (0xff : Nat) = 2 ^ 8 - 1 by norm_num]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow
    (byteFrom input.toList off.toNat).toNat_lt

theorem addmodValue_toNat (a b modulus : U256) (hmodulus : modulus ≠ 0) :
    (addmodValue a b modulus).toNat =
      (a.toNat + b.toNat) % modulus.toNat := by
  unfold addmodValue
  rw [if_neg hmodulus, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt
    ((Nat.mod_lt _ (Nat.pos_of_ne_zero (fun h => hmodulus
      (BitVec.eq_of_toNat_eq (by simpa using h))))).trans modulus.isLt)

theorem mulmodValue_toNat (a b modulus : U256) (hmodulus : modulus ≠ 0) :
    (mulmodValue a b modulus).toNat =
      (a.toNat * b.toNat) % modulus.toNat := by
  unfold mulmodValue
  rw [if_neg hmodulus, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt
    ((Nat.mod_lt _ (Nat.pos_of_ne_zero (fun h => hmodulus
      (BitVec.eq_of_toNat_eq (by simpa using h))))).trans modulus.isLt)

theorem basePrefix_correct (st : EvmState) (input : ByteArray)
    (baseOff modulus : U256) (count : Nat)
    (hcalldata : st.env.calldata = input.toList) (hmodulus : modulus ≠ 0)
    (hbound : baseOff.toNat + count < 2 ^ 256) :
    (basePrefix st baseOff modulus count).toNat =
      Precompile.bytesToNatPadded input baseOff.toNat count % modulus.toNat := by
  induction count with
  | zero => simp [basePrefix, Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width]
  | succ count ih =>
      rw [basePrefix, baseStep, addmodValue_toNat _ _ modulus hmodulus,
        mulmodValue_toNat _ _ modulus hmodulus, ih (by omega),
        Challenge.EvmProof.Bytes.bytesToNatPadded_succ]
      have hoff : (baseOff + BitVec.ofNat 256 count).toNat =
          baseOff.toNat + count := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : count < 2 ^ 256),
          Nat.mod_eq_of_lt (by omega : baseOff.toNat + count < 2 ^ 256)]
      rw [calldataByteValue_toNat st input _ hcalldata, hoff]
      rw [show ((256 : U256)).toNat = 256 by
        change 256 % 2 ^ 256 = 256
        rw [Nat.mod_eq_of_lt (by norm_num)]]
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
        Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

/-! ## Branchless square-and-multiply -/

def exponentBitNat (byte : U256) (j : Nat) : Nat :=
  (byte.toNat >>> (7 - j)) % 2

theorem exponentBitNat_zero_or_one (byte : U256) (j : Nat) :
    exponentBitNat byte j = 0 ∨ exponentBitNat byte j = 1 := by
  unfold exponentBitNat
  omega

theorem exponentBit_eq (byte : U256) (j : Nat) (hj : j < 8) :
    (byte >>> ((7 : U256) - BitVec.ofNat 256 j).toNat) &&& 1 =
      BitVec.ofNat 256 (exponentBitNat byte j) := by
  have hjword : (BitVec.ofNat 256 j).toNat = j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 256)]
  have hseven : ((7 : U256)).toNat = 7 := by rfl
  have hle : BitVec.ofNat 256 j ≤ (7 : U256) := by
    rw [BitVec.le_def, hjword, hseven]
    omega
  have hshift : (((7 : U256) - BitVec.ofNat 256 j).toNat) = 7 - j := by
    rw [BitVec.toNat_sub_of_le hle, hjword]
    rfl
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, hshift,
    show ((1 : U256)).toNat = 1 by rfl, BitVec.toNat_ofNat]
  unfold exponentBitNat
  rw [show (1 : Nat) = 2 ^ 1 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (by omega : (byte.toNat >>> (7 - j)) % 2 < 2 ^ 256)]

theorem select_zero (x y : U256) :
    x ^^^ (((x ^^^ y) &&& ((0 : U256) - 0))) = x := by
  simp

theorem select_one (x y : U256) :
    x ^^^ (((x ^^^ y) &&& ((0 : U256) - 1))) = y := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_xor]
  have hmask : (((0 : U256) - 1).toNat) = 2 ^ 256 - 1 := by
    rw [BitVec.toNat_sub]
    change (2 ^ 256 - 1 + 0) % 2 ^ 256 = 2 ^ 256 - 1
    norm_num
  rw [hmask, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (Nat.xor_lt_two_pow x.isLt y.isLt),
    ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

def natBitStep (modulus : Nat) (byte : U256) (j acc base : Nat) : Nat :=
  let square := (acc * acc) % modulus
  if exponentBitNat byte j = 0 then square else (square * base) % modulus

def natBitAfter (modulus : Nat) (byte : U256) (base : Nat) :
    Nat → Nat → Nat
  | 0, acc => acc
  | j + 1, acc => natBitStep modulus byte j
      (natBitAfter modulus byte base j acc) base

theorem bitStep_correct (acc base modulus byte : U256) (j : Nat)
    (hmodulus : modulus ≠ 0) (hj : j < 8) :
    (bitStep acc base modulus byte j).toNat =
      natBitStep modulus.toNat byte j acc.toNat base.toNat := by
  rcases exponentBitNat_zero_or_one byte j with hbit | hbit
  · unfold bitStep natBitStep
    rw [exponentBit_eq byte j hj, hbit]
    rw [show BitVec.ofNat 256 0 = (0 : U256) by rfl, if_pos rfl]
    rw [select_zero, mulmodValue_toNat _ _ modulus hmodulus]
  · unfold bitStep natBitStep
    rw [exponentBit_eq byte j hj, hbit]
    rw [show BitVec.ofNat 256 1 = (1 : U256) by rfl, if_neg (by omega)]
    rw [select_one, mulmodValue_toNat _ _ modulus hmodulus,
      mulmodValue_toNat _ _ modulus hmodulus]

theorem bitPrefix_correct (base modulus byte : U256) (j : Nat) (acc : U256)
    (hmodulus : modulus ≠ 0) (hj : j ≤ 8) :
    (bitPrefix base modulus byte j acc).toNat =
      natBitAfter modulus.toNat byte base.toNat j acc.toNat := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [bitPrefix, natBitAfter, bitStep_correct _ _ modulus byte j hmodulus (by omega),
        ih (by omega)]

def bitValuePrefix (byte : U256) : Nat → Nat
  | 0 => 0
  | j + 1 => 2 * bitValuePrefix byte j + exponentBitNat byte j

theorem bitValuePrefix_ofNat_eight (n : Nat) (hn : n < 256) :
    bitValuePrefix (BitVec.ofNat 256 n) 8 = n := by
  interval_cases n <;> decide

theorem bitValuePrefix_eight (byte : U256) (hbyte : byte.toNat < 256) :
    bitValuePrefix byte 8 = byte.toNat := by
  calc
    bitValuePrefix byte 8 = bitValuePrefix (BitVec.ofNat 256 byte.toNat) 8 := by
      congr 2
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt byte.isLt]
    _ = byte.toNat := bitValuePrefix_ofNat_eight byte.toNat hbyte

theorem natBitAfter_lt (modulus : Nat) (byte : U256) (base acc j : Nat)
    (hmodulus : 0 < modulus) (hacc : acc < modulus) :
    natBitAfter modulus byte base j acc < modulus := by
  induction j with
  | zero => exact hacc
  | succ j ih =>
      rw [natBitAfter, natBitStep]
      split <;> exact Nat.mod_lt _ hmodulus

theorem mul_mod_reduced (a b modulus : Nat) :
    ((a % modulus) * (b % modulus)) % modulus = (a * b) % modulus :=
  (Nat.mul_mod a b modulus).symm

theorem left_mod_mul (a b modulus : Nat) :
    ((a % modulus) * b) % modulus = (a * b) % modulus := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem natBitAfter_eq (modulus : Nat) (byte : U256) (base acc j : Nat)
    (hacc : acc < modulus) :
    natBitAfter modulus byte base j acc =
      (acc ^ (2 ^ j) * base ^ (bitValuePrefix byte j)) % modulus := by
  induction j with
  | zero => simp [natBitAfter, bitValuePrefix, Nat.mod_eq_of_lt hacc]
  | succ j ih =>
      rw [natBitAfter, natBitStep]
      rcases exponentBitNat_zero_or_one byte j with hbit | hbit
      · rw [if_pos hbit, ih, bitValuePrefix, hbit, Nat.add_zero]
        rw [mul_mod_reduced]
        congr 1
        simp only [Nat.pow_succ, Nat.pow_mul]
        ring
      · rw [if_neg (by omega), ih, bitValuePrefix, hbit]
        rw [mul_mod_reduced, left_mod_mul]
        congr 1
        simp only [Nat.pow_succ, Nat.pow_mul]
        ring

theorem bitPrefix_eight_correct (base modulus byte acc : U256)
    (hmodulus : modulus ≠ 0) (hacc : acc.toNat < modulus.toNat)
    (hbyte : byte.toNat < 256) :
    (bitPrefix base modulus byte 8 acc).toNat =
      (acc.toNat ^ 256 * base.toNat ^ byte.toNat) % modulus.toNat := by
  rw [bitPrefix_correct base modulus byte 8 acc hmodulus (by omega),
    natBitAfter_eq modulus.toNat byte base.toNat acc.toNat 8 hacc,
    bitValuePrefix_eight byte hbyte]
  norm_num

/-! ## Exponent bytes and modular exponentiation -/

def natExpStep (modulus byte acc base : Nat) : Nat :=
  (acc ^ 256 * base ^ byte) % modulus

def natExpAfter (input : ByteArray) (expOffset modulus base : Nat) :
    Nat → Nat → Nat
  | 0, acc => acc
  | i + 1, acc =>
      natExpStep modulus (byteFrom input.toList (expOffset + i)).toNat
        (natExpAfter input expOffset modulus base i acc) base

theorem natExpAfter_lt (input : ByteArray) (expOffset modulus base acc count : Nat)
    (hmodulus : 0 < modulus) (hacc : acc < modulus) :
    natExpAfter input expOffset modulus base count acc < modulus := by
  induction count with
  | zero => exact hacc
  | succ count ih =>
      rw [natExpAfter, natExpStep]
      exact Nat.mod_lt _ hmodulus

theorem exponentPrefix_to_natExpAfter (st : EvmState) (input : ByteArray)
    (expOff base modulus initial : U256) (count : Nat)
    (hcalldata : st.env.calldata = input.toList) (hmodulus : modulus ≠ 0)
    (hinitial : initial.toNat < modulus.toNat)
    (hbound : expOff.toNat + count < 2 ^ 256) :
    (exponentPrefix st expOff base modulus count initial).toNat =
      natExpAfter input expOff.toNat modulus.toNat base.toNat count initial.toNat := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hoff : (expOff + BitVec.ofNat 256 count).toNat =
          expOff.toNat + count := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : count < 2 ^ 256),
          Nat.mod_eq_of_lt (by omega : expOff.toNat + count < 2 ^ 256)]
      have hprefix :
          (exponentPrefix st expOff base modulus count initial).toNat <
            modulus.toNat := by
        rw [ih (by omega)]
        exact natExpAfter_lt input expOff.toNat modulus.toNat base.toNat initial.toNat
          count (Nat.pos_of_ne_zero (fun h => hmodulus
            (BitVec.eq_of_toNat_eq (by simpa using h)))) hinitial
      rw [exponentPrefix, exponentStep,
        bitPrefix_eight_correct base modulus
          (calldataByteValue st (expOff + BitVec.ofNat 256 count))
          (exponentPrefix st expOff base modulus count initial)
          hmodulus hprefix
          (by rw [calldataByteValue_toNat st input _ hcalldata, hoff]
              exact (byteFrom input.toList (expOff.toNat + count)).toNat_lt),
        natExpAfter, natExpStep, ih (by omega),
        calldataByteValue_toNat st input _ hcalldata, hoff]

theorem natExpAfter_eq (input : ByteArray) (expOffset modulus base acc count : Nat)
    (hacc : acc < modulus) :
    natExpAfter input expOffset modulus base count acc =
      (acc ^ (256 ^ count) *
        base ^ (Precompile.bytesToNatPadded input expOffset count)) % modulus := by
  induction count with
  | zero =>
      simp [natExpAfter, Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width,
        Nat.mod_eq_of_lt hacc]
  | succ count ih =>
      rw [natExpAfter, natExpStep, ih,
        Challenge.EvmProof.Bytes.bytesToNatPadded_succ]
      let a := acc ^ (256 ^ count)
      let b := base ^ (Precompile.bytesToNatPadded input expOffset count)
      let digit := (byteFrom input.toList (expOffset + count)).toNat
      calc
        (((a * b) % modulus) ^ 256 * base ^ digit) % modulus =
            ((((a * b) % modulus) ^ 256 % modulus) * base ^ digit) % modulus :=
          (left_mod_mul _ _ _).symm
        _ = (((a * b) ^ 256 % modulus) * base ^ digit) % modulus := by
          rw [← Nat.pow_mod]
        _ = ((a * b) ^ 256 * base ^ digit) % modulus :=
          left_mod_mul _ _ _
        _ = (acc ^ (256 ^ (count + 1)) *
              base ^
                (Precompile.bytesToNatPadded input expOffset count * 256 + digit)) %
              modulus := by
          congr 1
          simp only [a, b, Nat.pow_succ, Nat.pow_mul, Nat.pow_add]
          ring

theorem initialAccumulator_toNat (modulus : U256) (hmodulus : modulus ≠ 0) :
    (initialAccumulator modulus).toNat = 1 % modulus.toNat := by
  unfold initialAccumulator
  rw [if_neg hmodulus, BitVec.toNat_umod]
  rfl

theorem residue_power_eq_modPow (base exponent modulus count : Nat)
    (hmodulus : 0 < modulus) :
    (((1 % modulus) ^ (256 ^ count)) *
        ((base % modulus) ^ exponent)) % modulus =
      Precompile.modPow base exponent modulus := by
  rw [Algorithm.modPow_eq, if_neg (Nat.ne_of_gt hmodulus)]
  by_cases hm1 : modulus = 1
  · subst modulus
    simp [Nat.mod_one]
  · have hone : 1 < modulus := by omega
    rw [Nat.mod_eq_of_lt hone]
    simp only [one_pow, one_mul]
    exact (Nat.pow_mod base exponent modulus).symm

/-- The complete source exponent loop computes the pinned precompile's
`modPow`, provided its base word is the streamed base residue. -/
theorem exponentPrefix_correct (st : EvmState) (input : ByteArray)
    (expOff base modulus : U256) (count baseNat : Nat)
    (hcalldata : st.env.calldata = input.toList) (hmodulus : modulus ≠ 0)
    (hbase : base.toNat = baseNat % modulus.toNat)
    (hbound : expOff.toNat + count < 2 ^ 256) :
    (exponentPrefix st expOff base modulus count
        (initialAccumulator modulus)).toNat =
      Precompile.modPow baseNat
        (Precompile.bytesToNatPadded input expOff.toNat count) modulus.toNat := by
  have hmodpos : 0 < modulus.toNat :=
    Nat.pos_of_ne_zero (fun h => hmodulus (BitVec.eq_of_toNat_eq (by simpa using h)))
  have hacc : (initialAccumulator modulus).toNat < modulus.toNat := by
    rw [initialAccumulator_toNat modulus hmodulus]
    exact Nat.mod_lt _ hmodpos
  rw [exponentPrefix_to_natExpAfter st input expOff base modulus
      (initialAccumulator modulus) count hcalldata hmodulus hacc hbound,
    natExpAfter_eq input expOff.toNat modulus.toNat base.toNat
      (initialAccumulator modulus).toNat count hacc,
    initialAccumulator_toNat modulus hmodulus, hbase]
  exact residue_power_eq_modPow baseNat
    (Precompile.bytesToNatPadded input expOff.toNat count) modulus.toNat count hmodpos

/-! ## Input modulus and fixed-width serialization -/

theorem wordModulus_toNat (st : EvmState) (input : ByteArray)
    (modulusSize modOffset : Nat)
    (hcalldata : st.env.calldata = input.toList) (hword : modulusSize ≤ 32)
    (hoffset : modOffset < 2 ^ 256) :
    (wordModulus st (BitVec.ofNat 256 modulusSize)
        (BitVec.ofNat 256 modOffset)).toNat =
      Precompile.bytesToNatPadded input modOffset modulusSize := by
  have hmsize : (BitVec.ofNat 256 modulusSize).toNat = modulusSize := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : modulusSize < 2 ^ 256)]
  have hoff : (BitVec.ofNat 256 modOffset).toNat = modOffset := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoffset]
  have hle : BitVec.ofNat 256 modulusSize ≤ (32 : U256) := by
    rw [BitVec.le_def, hmsize]
    exact hword
  have hshift :
      (((32 : U256) - BitVec.ofNat 256 modulusSize) * 8).toNat =
        (32 - modulusSize) * 8 := by
    rw [BitVec.toNat_mul, BitVec.toNat_sub_of_le hle, hmsize]
    change ((32 - modulusSize) * 8) % 2 ^ 256 = (32 - modulusSize) * 8
    rw [Nat.mod_eq_of_lt (by omega)]
  unfold wordModulus
  rw [BitVec.toNat_ushiftRight, hshift, hoff, hcalldata, wordFrom_toNat]
  simpa [Challenge.EvmProof.Bytes.readWord_toNat] using
    Challenge.EvmProof.Bytes.readWord_shift_toNat input modOffset modulusSize hword

theorem shiftedWord_toNat (value : U256) (width : Nat)
    (hwidth : width ≤ 32) (hvalue : value.toNat < 256 ^ width) :
    (value <<< (((32 : U256) - BitVec.ofNat 256 width) * 8).toNat).toNat =
      value.toNat * 256 ^ (32 - width) := by
  have hwidthWord : (BitVec.ofNat 256 width).toNat = width := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : width < 2 ^ 256)]
  have hle : BitVec.ofNat 256 width ≤ (32 : U256) := by
    rw [BitVec.le_def, hwidthWord]
    exact hwidth
  have hshift :
      (((32 : U256) - BitVec.ofNat 256 width) * 8).toNat =
        (32 - width) * 8 := by
    rw [BitVec.toNat_mul, BitVec.toNat_sub_of_le hle, hwidthWord]
    change ((32 - width) * 8) % 2 ^ 256 = (32 - width) * 8
    rw [Nat.mod_eq_of_lt (by omega)]
  have hfactor : 0 < 256 ^ (32 - width) := pow_pos (by norm_num) _
  have hbound : value.toNat * 256 ^ (32 - width) < 2 ^ 256 := by
    rw [show (2 : Nat) ^ 256 = 256 ^ 32 by norm_num]
    calc
      value.toNat * 256 ^ (32 - width) <
          256 ^ width * 256 ^ (32 - width) :=
        Nat.mul_lt_mul_of_pos_right hvalue hfactor
      _ = 256 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
  rw [BitVec.toNat_shiftLeft, hshift, Nat.shiftLeft_eq]
  rw [show (2 : Nat) ^ ((32 - width) * 8) = 256 ^ (32 - width) by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]
    congr 1
    omega]
  exact Nat.mod_eq_of_lt hbound

theorem shifted_div (n width k : Nat) (hwidth : width ≤ 32) (hk : k < width) :
    n * 256 ^ (32 - width) / 256 ^ (32 - 1 - k) =
      n / 256 ^ (width - 1 - k) := by
  have hexponent : 32 - 1 - k = (32 - width) + (width - 1 - k) := by omega
  rw [hexponent, Nat.pow_add, Nat.mul_comm (256 ^ (32 - width))]
  exact Nat.mul_div_mul_right n (256 ^ (width - 1 - k))
    (pow_pos (by norm_num) _)

theorem outputMemory_readPadded (value : U256) (width : Nat)
    (hwidth : width ≤ 32) (hvalue : value.toNat < 256 ^ width) :
    let shifted := value <<<
      (((32 : U256) - BitVec.ofNat 256 width) * 8).toNat
    MachineState.readPadded
        (MachineState.writeBytes ByteArray.empty
          (Data.Bytes.natToBytesPadded shifted.toNat 32) 0x1800)
        0x1800 width =
      Precompile.natToBytes value.toNat width := by
  dsimp only
  apply ByteArray.ext_getElem
  · rw [Challenge.EvmProof.Memory.readPadded_size, Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro k hleft hright
    have hk : k < width := by
      simpa [Precompile.natToBytes,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hright
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hk,
      MachineState.writeBytes_getElem?_getD, if_pos (by
        constructor
        · omega
        · simp [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
          omega)]
    rw [show 0x1800 + k - 0x1800 = k by omega,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ 32 k
        (by omega),
      Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ width k hk,
      shiftedWord_toNat value width hwidth hvalue,
      shifted_div value.toNat width k hwidth hk]

theorem readBytes_storeWord_output (memory : Nat → UInt8) (value : U256)
    (width : Nat) (hmemory : memory = fun _ => 0)
    (hwidth : width ≤ 32) (hvalue : value.toNat < 256 ^ width) :
    let shifted := value <<<
      (((32 : U256) - BitVec.ofNat 256 width) * 8).toNat
    readBytes (storeWord memory 0x1800 shifted) 0x1800 width =
      (Precompile.natToBytes value.toNat width).toList := by
  dsimp only
  subst memory
  let shifted := value <<< (((32 : U256) - BitVec.ofNat 256 width) * 8).toNat
  have hmatch := YulEvmCompiler.MemMatch.init.storeWord 0x1800 shifted
  rw [hmatch.readBytes 0x1800 width]
  exact congrArg ByteArray.toList
    (outputMemory_readPadded value width hwidth hvalue)

/-! ## The complete word-path result -/

def expOffset (input : ByteArray) : Nat := 96 + baseSize input

def modulusOffset (input : ByteArray) : Nat :=
  expOffset input + exponentSize input

def baseNat (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input 96 (baseSize input)

def exponentNat (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input (expOffset input) (exponentSize input)

def modulusNat (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input (modulusOffset input) (modulusSize input)

def sourceModulus (st : EvmState) (input : ByteArray) : U256 :=
  wordModulus st (BitVec.ofNat 256 (modulusSize input))
    (BitVec.ofNat 256 (modulusOffset input))

def sourceBase (st : EvmState) (input : ByteArray) : U256 :=
  basePrefix st (BitVec.ofNat 256 96) (sourceModulus st input) (baseSize input)

def sourceWordResult (st : EvmState) (input : ByteArray) : U256 :=
  exponentPrefix st (BitVec.ofNat 256 (expOffset input)) (sourceBase st input)
    (sourceModulus st input) (exponentSize input)
    (initialAccumulator (sourceModulus st input))

theorem sourceModulus_toNat (st : EvmState) (input : ByteArray)
    (hcalldata : st.env.calldata = input.toList) (hvalid : ValidInput input)
    (hword : modulusSize input ≤ 32) :
    (sourceModulus st input).toNat = modulusNat input := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  apply wordModulus_toNat st input (modulusSize input) (modulusOffset input)
    hcalldata hword
  simp only [modulusOffset, expOffset]
  omega

theorem sourceModulus_nonzero (st : EvmState) (input : ByteArray)
    (hcalldata : st.env.calldata = input.toList) (hvalid : ValidInput input)
    (hword : modulusSize input ≤ 32) (hmodulus : modulusNat input ≠ 0) :
    sourceModulus st input ≠ 0 := by
  intro hzero
  have hnat := congrArg BitVec.toNat hzero
  rw [sourceModulus_toNat st input hcalldata hvalid hword] at hnat
  exact hmodulus hnat

theorem sourceBase_correct (st : EvmState) (input : ByteArray)
    (hcalldata : st.env.calldata = input.toList) (hvalid : ValidInput input)
    (hword : modulusSize input ≤ 32) (hmodulus : modulusNat input ≠ 0) :
    (sourceBase st input).toNat = baseNat input % modulusNat input := by
  have hmodword := sourceModulus_nonzero st input hcalldata hvalid hword hmodulus
  have hb := hvalid.2.1
  rw [sourceBase, basePrefix_correct st input (BitVec.ofNat 256 96)
      (sourceModulus st input) (baseSize input) hcalldata hmodword (by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num : 96 < 2 ^ 256)]
        omega),
    sourceModulus_toNat st input hcalldata hvalid hword]
  rfl

theorem sourceWordResult_correct (st : EvmState) (input : ByteArray)
    (hcalldata : st.env.calldata = input.toList) (hvalid : ValidInput input)
    (hword : modulusSize input ≤ 32) (hmodulus : modulusNat input ≠ 0) :
    (sourceWordResult st input).toNat =
      Precompile.modPow (baseNat input) (exponentNat input) (modulusNat input) := by
  have hmodword := sourceModulus_nonzero st input hcalldata hvalid hword hmodulus
  have hb := hvalid.2.1
  have he := hvalid.2.2.1
  have hoff : expOffset input < 2 ^ 256 := by
    simp only [expOffset]
    omega
  rw [sourceWordResult,
    exponentPrefix_correct st input (BitVec.ofNat 256 (expOffset input))
      (sourceBase st input) (sourceModulus st input) (exponentSize input)
      (baseNat input) hcalldata hmodword
      (by rw [sourceBase_correct st input hcalldata hvalid hword hmodulus,
          sourceModulus_toNat st input hcalldata hvalid hword])
      (by
        rw [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt hoff]
        simp only [expOffset]
        omega),
    sourceModulus_toNat st input hcalldata hvalid hword,
    show (BitVec.ofNat 256 (expOffset input)).toNat = expOffset input by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]]
  rfl

/-- Fresh-memory serialization of the direct source word path agrees exactly
with `Challenge.Modexp.spec`.  This is the endpoint consumed by the source
execution proof after `eval_modexpWord_nonzero`. -/
theorem wordReturnedState_result (st : EvmState) (input : ByteArray)
    (hmemory : st.memory = fun _ => 0)
    (hcalldata : st.env.calldata = input.toList) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodulus : modulusNat input ≠ 0) :
    (wordReturnedState st (BitVec.ofNat 256 (modulusSize input))
      (sourceWordResult st input)).halted =
        some (HaltKind.ret, (spec input).toList) := by
  have hmsizeWord : (BitVec.ofNat 256 (modulusSize input)).toNat =
      modulusSize input := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : modulusSize input < 2 ^ 256)]
  have hmodpos : 0 < modulusNat input := Nat.pos_of_ne_zero hmodulus
  have hmodwidth : modulusNat input < 256 ^ modulusSize input :=
    Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input
      (modulusOffset input) (modulusSize input)
  let result := Precompile.modPow (baseNat input) (exponentNat input) (modulusNat input)
  have hresult : result < 256 ^ modulusSize input :=
    (Algorithm.modPow_lt hmodpos).trans hmodwidth
  have hsource : (sourceWordResult st input).toNat = result :=
    sourceWordResult_correct st input hcalldata hvalid hword hmodulus
  change some (HaltKind.ret,
      readBytes
        (storeWord st.memory 0x1800
          (sourceWordResult st input <<<
            (((32 : U256) - BitVec.ofNat 256 (modulusSize input)) * 8).toNat))
        0x1800 (BitVec.ofNat 256 (modulusSize input)).toNat) = _
  rw [hmsizeWord,
    readBytes_storeWord_output st.memory (sourceWordResult st input)
      (modulusSize input) hmemory hword (by simpa [hsource] using hresult)]
  rw [hsource, spec, if_neg (Nat.ne_of_gt hmsize)]
  congr 2

end Challenge.Modexp.Reference.Proofs.Yul.WordMath
