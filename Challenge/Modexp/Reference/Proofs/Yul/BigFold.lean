import Challenge.Modexp.Reference.Proofs.Algorithm
import Challenge.EvmProof.Bytes
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Pure fold arithmetic for the direct MODEXP Yul proof

This module contains the MODEXP-specific arithmetic behind the two nested
byte/bit loops in `modexpBig` and the limb/bit loops in `mulModBig`.  It does
not mention Yul execution or import the bytecode proof: execution certificates
can target these small recurrences and then use the closed forms below.
-/

namespace Challenge.Modexp.Reference.Proofs.Yul.BigFold

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM

/-! ## Little-endian limbs as one stream of multiplier bits -/

/-- Expand little-endian 256-bit limbs into one little-endian bit stream. -/
def limbBitDigits (limbs : List Nat) : List Nat :=
  limbs.flatMap (Nat.digitsAppend 2 256)

@[simp] theorem limbBitDigits_nil : limbBitDigits [] = [] := rfl

@[simp] theorem limbBitDigits_cons (limb : Nat) (limbs : List Nat) :
    limbBitDigits (limb :: limbs) =
      Nat.digitsAppend 2 256 limb ++ limbBitDigits limbs := rfl

@[simp] theorem length_limbBitDigits {limbs : List Nat}
    (hlimbs : ∀ limb ∈ limbs, limb < 2 ^ 256) :
    (limbBitDigits limbs).length = 256 * limbs.length := by
  induction limbs with
  | nil => simp
  | cons limb limbs ih =>
      have hlimb : limb < 2 ^ 256 := hlimbs limb (by simp)
      have htail : ∀ digit ∈ limbs, digit < 2 ^ 256 := by
        intro digit hdigit
        exact hlimbs digit (by simp [hdigit])
      rw [limbBitDigits_cons, List.length_append,
        Nat.length_digitsAppend (by norm_num) 256 hlimb, ih htail,
        List.length_cons]
      omega

/-- Flattening fixed-width word digits preserves their radix value. -/
theorem value_limbBitDigits (limbs : List Nat)
    (hlimbs : ∀ limb ∈ limbs, limb < 2 ^ 256) :
    Nat.ofDigits 2 (limbBitDigits limbs) =
      Nat.ofDigits (2 ^ 256) limbs := by
  induction limbs with
  | nil => simp [limbBitDigits]
  | cons limb limbs ih =>
      have hlimb : limb < 2 ^ 256 := hlimbs limb (by simp)
      have htail : ∀ digit ∈ limbs, digit < 2 ^ 256 := by
        intro digit hdigit
        exact hlimbs digit (by simp [hdigit])
      rw [limbBitDigits_cons, Nat.ofDigits_append,
        Nat.length_digitsAppend (by norm_num) 256 hlimb,
        Nat.digitsAppend, Nat.ofDigits_append_replicate_zero,
        Nat.ofDigits_digits, ih htail, Nat.ofDigits_cons]

/-- The double-and-add recurrence starting from zero multiplies the addend by
the natural value of its selector-bit stream. -/
theorem mulBits_zero_fst (modulus addend : Nat) (bits : List Nat)
    (hmodulus : 0 < modulus) (haddend : addend < modulus) :
    (Algorithm.mulBits modulus 0 addend bits).1 =
      (addend * Nat.ofDigits 2 bits) % modulus := by
  have hlt := (Algorithm.mulBits_lt (modulus := modulus) (acc := 0)
    (addend := addend) bits hmodulus (by omega) haddend).1
  have hvalue := Algorithm.mulBits_fst modulus 0 addend bits
  rw [Nat.mod_eq_of_lt hlt] at hvalue
  simpa [Nat.mul_comm] using hvalue

/-- The same result when the selector stream is obtained from fixed-width
little-endian limbs. -/
theorem mulLimbBits_zero_fst (modulus addend : Nat) (limbs : List Nat)
    (hmodulus : 0 < modulus) (haddend : addend < modulus)
    (hlimbs : ∀ limb ∈ limbs, limb < 2 ^ 256) :
    (Algorithm.mulBits modulus 0 addend (limbBitDigits limbs)).1 =
      (addend * Nat.ofDigits (2 ^ 256) limbs) % modulus := by
  rw [mulBits_zero_fst modulus addend (limbBitDigits limbs) hmodulus haddend,
    value_limbBitDigits limbs hlimbs]

/-! ## Big-endian byte bits -/

/-- Bit `j` of a byte in the source loop's most-significant-first order. -/
def msbBit (byte j : Nat) : Nat := byte / 2 ^ (7 - j) % 2

theorem msbBit_lt_two (byte j : Nat) : msbBit byte j < 2 := by
  exact Nat.mod_lt _ (by omega)

theorem msbBit_zero_or_one (byte j : Nat) :
    msbBit byte j = 0 ∨ msbBit byte j = 1 := by
  have := msbBit_lt_two byte j
  omega

/-- Value of the first `steps` most-significant bits of a byte. -/
def byteBitPrefix (byte : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => 2 * byteBitPrefix byte j + msbBit byte j

theorem byteBitPrefix_eight (byte : Nat) (hbyte : byte < 256) :
    byteBitPrefix byte 8 = byte := by
  interval_cases byte <;> decide

/-! ## Horner conversion of base bytes -/

/-- The arithmetic effect of the source base-conversion bit loop. -/
def hornerBitAfter (modulus byte : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | j + 1, acc =>
      (2 * hornerBitAfter modulus byte j acc + msbBit byte j) % modulus

theorem hornerBitAfter_lt (modulus byte steps acc : Nat)
    (hmodulus : 0 < modulus) (hacc : acc < modulus) :
    hornerBitAfter modulus byte steps acc < modulus := by
  induction steps with
  | zero => exact hacc
  | succ steps _ =>
      rw [hornerBitAfter]
      exact Nat.mod_lt _ hmodulus

theorem hornerBitAfter_eq (modulus byte steps acc : Nat)
    (hacc : acc < modulus) :
    hornerBitAfter modulus byte steps acc =
      (acc * 2 ^ steps + byteBitPrefix byte steps) % modulus := by
  induction steps with
  | zero => simp [hornerBitAfter, byteBitPrefix, Nat.mod_eq_of_lt hacc]
  | succ steps ih =>
      rw [hornerBitAfter, ih, byteBitPrefix]
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
        ← Nat.add_mod]
      congr 1
      simp only [pow_succ]
      ring

theorem hornerBitAfter_eight (modulus byte acc : Nat)
    (hacc : acc < modulus) (hbyte : byte < 256) :
    hornerBitAfter modulus byte 8 acc =
      (acc * 256 + byte) % modulus := by
  rw [hornerBitAfter_eq modulus byte 8 acc hacc,
    byteBitPrefix_eight byte hbyte]
  norm_num

/-- Stream input bytes through the source's base-conversion recurrence. -/
def baseByteAfter (input : ByteArray) (baseOffset modulus : Nat) :
    Nat → Nat → Nat
  | 0, acc => acc
  | i + 1, acc =>
      (baseByteAfter input baseOffset modulus i acc * 256 +
        (byteFrom input.toList (baseOffset + i)).toNat) % modulus

theorem baseByteAfter_lt (input : ByteArray)
    (baseOffset modulus steps acc : Nat) (hmodulus : 0 < modulus)
    (hacc : acc < modulus) :
    baseByteAfter input baseOffset modulus steps acc < modulus := by
  induction steps with
  | zero => exact hacc
  | succ steps _ =>
      rw [baseByteAfter]
      exact Nat.mod_lt _ hmodulus

theorem baseByteAfter_eq (input : ByteArray)
    (baseOffset modulus steps acc : Nat) (hacc : acc < modulus) :
    baseByteAfter input baseOffset modulus steps acc =
      (acc * 256 ^ steps +
        Precompile.bytesToNatPadded input baseOffset steps) % modulus := by
  induction steps with
  | zero =>
      simp [baseByteAfter, Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width,
        Nat.mod_eq_of_lt hacc]
  | succ steps ih =>
      rw [baseByteAfter, ih,
        Challenge.EvmProof.Bytes.bytesToNatPadded_succ]
      let prior := acc * 256 ^ steps +
        Precompile.bytesToNatPadded input baseOffset steps
      let digit := (byteFrom input.toList (baseOffset + steps)).toNat
      calc
        ((prior % modulus) * 256 + digit) % modulus =
            (((prior % modulus) * 256) % modulus + digit % modulus) %
              modulus := Nat.add_mod _ _ _
        _ = ((prior * 256) % modulus + digit % modulus) % modulus := by
          rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
        _ = (prior * 256 + digit) % modulus := (Nat.add_mod _ _ _).symm
        _ = (acc * 256 ^ (steps + 1) +
              (Precompile.bytesToNatPadded input baseOffset steps * 256 +
                digit)) % modulus := by
          congr 1
          simp only [prior, pow_succ]
          ring

theorem baseByteAfter_zero_eq (input : ByteArray)
    (baseOffset modulus steps : Nat) (hmodulus : 0 < modulus) :
    baseByteAfter input baseOffset modulus steps 0 =
      Precompile.bytesToNatPadded input baseOffset steps % modulus := by
  rw [baseByteAfter_eq input baseOffset modulus steps 0 (by omega)]
  simp

/-! ## Square-and-multiply exponent bytes -/

/-- Arithmetic effect of one exponent bit. -/
def powBitStep (modulus byte j acc base : Nat) : Nat :=
  let square := (acc * acc) % modulus
  if msbBit byte j = 0 then square else (square * base) % modulus

/-- Arithmetic effect of a prefix of one exponent byte. -/
def powBitAfter (modulus byte base : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | j + 1, acc =>
      powBitStep modulus byte j (powBitAfter modulus byte base j acc) base

theorem powBitAfter_lt (modulus byte base steps acc : Nat)
    (hmodulus : 0 < modulus) (hacc : acc < modulus) :
    powBitAfter modulus byte base steps acc < modulus := by
  induction steps with
  | zero => exact hacc
  | succ steps _ =>
      rw [powBitAfter, powBitStep]
      split <;> exact Nat.mod_lt _ hmodulus

theorem mul_mod_reduced (a b modulus : Nat) :
    ((a % modulus) * (b % modulus)) % modulus = (a * b) % modulus :=
  (Nat.mul_mod a b modulus).symm

theorem left_mod_mul (a b modulus : Nat) :
    ((a % modulus) * b) % modulus = (a * b) % modulus := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem powBitAfter_eq (modulus byte base steps acc : Nat)
    (hacc : acc < modulus) :
    powBitAfter modulus byte base steps acc =
      (acc ^ (2 ^ steps) * base ^ (byteBitPrefix byte steps)) % modulus := by
  induction steps with
  | zero => simp [powBitAfter, byteBitPrefix, Nat.mod_eq_of_lt hacc]
  | succ steps ih =>
      rw [powBitAfter, powBitStep]
      rcases msbBit_zero_or_one byte steps with hbit | hbit
      · rw [if_pos hbit, ih, byteBitPrefix, hbit, Nat.add_zero]
        rw [mul_mod_reduced]
        congr 1
        simp only [pow_succ, Nat.pow_mul]
        ring
      · rw [if_neg (by omega), ih, byteBitPrefix, hbit]
        rw [mul_mod_reduced, left_mod_mul]
        congr 1
        simp only [pow_succ, Nat.pow_mul]
        ring

/-- Eight source iterations implement one base-256 exponent digit. -/
theorem powBitAfter_eight (modulus byte base acc : Nat)
    (hacc : acc < modulus) (hbyte : byte < 256) :
    powBitAfter modulus byte base 8 acc =
      (acc ^ 256 * base ^ byte) % modulus := by
  rw [powBitAfter_eq modulus byte base 8 acc hacc,
    byteBitPrefix_eight byte hbyte]
  norm_num

/-- Stream exponent bytes through square-and-multiply. -/
def exponentByteAfter (input : ByteArray) (exponentOffset modulus base : Nat) :
    Nat → Nat → Nat
  | 0, acc => acc
  | i + 1, acc =>
      let byte := (byteFrom input.toList (exponentOffset + i)).toNat
      (exponentByteAfter input exponentOffset modulus base i acc ^ 256 *
        base ^ byte) % modulus

theorem exponentByteAfter_lt (input : ByteArray)
    (exponentOffset modulus base steps acc : Nat) (hmodulus : 0 < modulus)
    (hacc : acc < modulus) :
    exponentByteAfter input exponentOffset modulus base steps acc < modulus := by
  induction steps with
  | zero => exact hacc
  | succ steps _ =>
      rw [exponentByteAfter]
      exact Nat.mod_lt _ hmodulus

theorem exponentByteAfter_eq (input : ByteArray)
    (exponentOffset modulus base steps acc : Nat) (hacc : acc < modulus) :
    exponentByteAfter input exponentOffset modulus base steps acc =
      (acc ^ (256 ^ steps) *
        base ^ (Precompile.bytesToNatPadded input exponentOffset steps)) %
          modulus := by
  induction steps with
  | zero =>
      simp [exponentByteAfter,
        Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width,
        Nat.mod_eq_of_lt hacc]
  | succ steps ih =>
      rw [exponentByteAfter, ih,
        Challenge.EvmProof.Bytes.bytesToNatPadded_succ]
      let a := acc ^ (256 ^ steps)
      let b := base ^
        (Precompile.bytesToNatPadded input exponentOffset steps)
      let digit := (byteFrom input.toList (exponentOffset + steps)).toNat
      calc
        (((a * b) % modulus) ^ 256 * base ^ digit) % modulus =
            ((((a * b) % modulus) ^ 256 % modulus) * base ^ digit) % modulus :=
          (left_mod_mul _ _ _).symm
        _ = (((a * b) ^ 256 % modulus) * base ^ digit) % modulus := by
          rw [← Nat.pow_mod]
        _ = ((a * b) ^ 256 * base ^ digit) % modulus :=
          left_mod_mul _ _ _
        _ = (acc ^ (256 ^ (steps + 1)) *
              base ^
                (Precompile.bytesToNatPadded input exponentOffset steps * 256 +
                  digit)) % modulus := by
          congr 1
          simp only [a, b, Nat.pow_succ, Nat.pow_mul, Nat.pow_add]
          ring

/-- Starting from `1 mod modulus` and a reduced base, the complete source
exponent fold is the pinned precompile result. -/
theorem exponentByteAfter_eq_modPow (input : ByteArray)
    (exponentOffset base modulus steps : Nat) (hmodulus : 0 < modulus) :
    exponentByteAfter input exponentOffset modulus (base % modulus) steps
        (1 % modulus) =
      Precompile.modPow base
        (Precompile.bytesToNatPadded input exponentOffset steps) modulus := by
  have hacc : 1 % modulus < modulus := Nat.mod_lt _ hmodulus
  rw [exponentByteAfter_eq input exponentOffset modulus (base % modulus)
    steps (1 % modulus) hacc]
  rw [Algorithm.modPow_eq, if_neg (Nat.ne_of_gt hmodulus)]
  by_cases hm1 : modulus = 1
  · subst modulus
    simp only [Nat.mod_one]
  · have hone : 1 < modulus := by omega
    rw [Nat.mod_eq_of_lt hone]
    simp only [one_pow, one_mul]
    exact (Nat.pow_mod base
      (Precompile.bytesToNatPadded input exponentOffset steps) modulus).symm

end Challenge.Modexp.Reference.Proofs.Yul.BigFold
