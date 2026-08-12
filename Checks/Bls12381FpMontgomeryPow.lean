import Challenge.Bls12381.ProofSupport.FpMontgomeryPowLawful
import Challenge.Bls12381.ProofSupport.FpMontgomeryPowSourceBits

set_option warningAsError true

namespace Checks.Bls12381FpMontgomeryPow

open Challenge.Bls12381.ProofSupport

example : Fp.scanExponent [] = none := rfl

example : Fp.scanExponent [0, 0] = none := rfl

example : Fp.highestSetBit (UInt8.ofNat 1) = 0 := rfl
example : Fp.highestSetBit (UInt8.ofNat 2) = 1 := rfl
example : Fp.highestSetBit (UInt8.ofNat 128) = 7 := rfl

example : Fp.scanExponent [0, 5, 2] = some
    (UInt8.ofNat 5,
      [false, true, false, false, false, false, false, false, true, false]) :=
  rfl

/-! Universal bridge from the source's SHR/AND/decrement loops to the compact
bit-list model used by the arithmetic invariant. -/

example : Fp.sourceByteBit (UInt8.ofNat 5) 2 = true := rfl
example : Fp.sourceByteBit (UInt8.ofNat 5) 1 = false := rfl
example : Fp.sourceTopBit (UInt8.ofNat 128) = 7 := rfl
example : Fp.sourceTopBit (UInt8.ofNat 5) = 2 := rfl

example (byte : UInt8) (hnonzero : byte.toNat ≠ 0) :
    Fp.sourceTopBit byte = Fp.highestSetBit byte :=
  Fp.sourceTopBit_eq_highestSetBit byte hnonzero

example (byte : UInt8) :
    Fp.sourceFirstRemainingBits byte = (Fp.significantByteBits byte).tail :=
  Fp.sourceFirstRemainingBits_eq byte

example (byte : UInt8) : Fp.sourceLaterByteBits byte = Fp.byteBits byte :=
  Fp.sourceLaterByteBits_eq byte

example (bytes : List UInt8) :
    Fp.sourceScanExponent bytes = Fp.scanExponent bytes :=
  Fp.sourceScanExponent_eq bytes

example (byte : UInt8) : (Fp.byteBits byte).length = 8 :=
  Fp.length_byteBits byte

example (byte : UInt8) :
    Fp.binaryValue (Fp.significantByteBits byte) = byte.toNat :=
  Fp.binaryValue_significantByteBits byte

example (byte : UInt8) : Fp.binaryValue (Fp.byteBits byte) = byte.toNat :=
  Fp.binaryValue_byteBits byte

example (bytes : List UInt8) :
    Fp.bytesValue (Fp.dropLeadingZeroBytes bytes) = Fp.bytesValue bytes :=
  Fp.bytesValue_dropLeadingZeroBytes bytes

example (bytes : List UInt8) :
    Fp.binaryValue (Fp.exponentBits bytes) = Fp.bytesValue bytes :=
  Fp.binaryValue_exponentBits bytes

example {bytes : List UInt8} {first : UInt8} {remaining : List Bool}
    (hscan : Fp.scanExponent bytes = some (first, remaining)) :
    Fp.bytesValue bytes = 2 ^ remaining.length + Fp.binaryValue remaining :=
  Fp.scanExponent_value hscan

example {bytes : List UInt8} (hscan : Fp.scanExponent bytes = none) :
    Fp.bytesValue bytes = 0 :=
  Fp.scanExponent_none_value hscan

/-! The loop squares before its conditional multiply and consumes bits in
source order after the initial most-significant one. -/

example (baseM acc : Fp.Limbs) :
    Fp.montgomeryBitStep baseM acc false = Fp.montMul2 acc acc :=
  rfl

example (baseM acc : Fp.Limbs) :
    Fp.montgomeryBitStep baseM acc true =
      Fp.montMul2 (Fp.montMul2 acc acc) baseM :=
  rfl

example (base : Fp.Limbs) : Fp.montgomeryPow base [] = Fp.montgomeryOne :=
  rfl

example (base : Fp.Limbs) : Fp.montgomeryPow base [0, 0] = Fp.montgomeryOne :=
  rfl

example (base : Fp.Limbs) :
    Fp.montgomeryPow base [1] = Fp.montgomeryEncode base :=
  rfl

example (base : Fp.Limbs) (exponent : List UInt8) :
    Fp.montgomeryPow base exponent =
      let baseM := Fp.montgomeryEncode base
      match Fp.sourceScanExponent exponent with
      | none => Fp.montgomeryOne
      | some (_, bits) => Fp.foldMontgomeryBits baseM baseM bits :=
  rfl

/-! Lawful accumulator and decoded-result refinement. -/

example {baseM acc : Fp.Limbs} (hbaseM : Fp.Canonical baseM)
    (hacc : Fp.Canonical acc) {baseValue : PrimeField.LawfulFp}
    {power : Nat}
    (hbase : (Fp.value baseM : PrimeField.LawfulFp) =
      baseValue * (Fp.montgomeryRadix : PrimeField.LawfulFp))
    (haccValue : (Fp.value acc : PrimeField.LawfulFp) =
      baseValue ^ power * (Fp.montgomeryRadix : PrimeField.LawfulFp))
    (bit : Bool) :
    (Fp.value (Fp.montgomeryBitStep baseM acc bit) : PrimeField.LawfulFp) =
      baseValue ^ (2 * power + bit.toNat) *
        (Fp.montgomeryRadix : PrimeField.LawfulFp) :=
  Fp.lawful_montgomeryBitStep hbaseM hacc hbase haccValue bit

example {baseM acc : Fp.Limbs} (hbaseM : Fp.Canonical baseM)
    (hacc : Fp.Canonical acc) {baseValue : PrimeField.LawfulFp}
    {power : Nat}
    (hbase : (Fp.value baseM : PrimeField.LawfulFp) =
      baseValue * (Fp.montgomeryRadix : PrimeField.LawfulFp))
    (haccValue : (Fp.value acc : PrimeField.LawfulFp) =
      baseValue ^ power * (Fp.montgomeryRadix : PrimeField.LawfulFp))
    (bits : List Bool) :
    (Fp.value (Fp.foldMontgomeryBits baseM acc bits) :
      PrimeField.LawfulFp) =
      baseValue ^ (power * 2 ^ bits.length + Fp.binaryValue bits) *
        (Fp.montgomeryRadix : PrimeField.LawfulFp) :=
  Fp.lawful_foldMontgomeryBits hbaseM hacc hbase haccValue bits

example {base : Fp.Limbs} (hbase : Fp.Canonical base)
    (exponent : List UInt8) :
    (Fp.value (Fp.montgomeryPow base exponent) : PrimeField.LawfulFp) =
      (Fp.value base : PrimeField.LawfulFp) ^ Fp.bytesValue exponent *
        (Fp.montgomeryRadix : PrimeField.LawfulFp) :=
  Fp.lawful_montgomeryPow hbase exponent

example {base : Fp.Limbs} (hbase : Fp.Canonical base)
    (exponent : List UInt8) :
    (Fp.value (Fp.montgomeryPowDecoded base exponent) :
      PrimeField.LawfulFp) =
      (Fp.value base : PrimeField.LawfulFp) ^ Fp.bytesValue exponent :=
  Fp.lawful_montgomeryPowDecoded hbase exponent

example {base : Fp.Limbs} (hbase : Fp.Canonical base)
    (exponent : List UInt8) :
    Fp.Canonical (Fp.montgomeryPowDecoded base exponent) :=
  Fp.canonical_montgomeryPowDecoded hbase exponent

example (base : Fp.Limbs) (exponent : ByteArray) :
    Fp.montgomeryPowBytes base exponent =
      Fp.montgomeryPow base exponent.toList :=
  rfl

example (exponent : ByteArray) :
    Fp.bytesValueArray exponent = Fp.bytesValue exponent.toList :=
  rfl

example {base : Fp.Limbs} (hbase : Fp.Canonical base)
    (exponent : ByteArray) :
    Fp.Canonical (Fp.montgomeryPowBytes base exponent) :=
  Fp.canonical_montgomeryPowBytes hbase exponent

example {base : Fp.Limbs} (hbase : Fp.Canonical base)
    (exponent : ByteArray) :
    (Fp.value (Fp.montgomeryPowBytes base exponent) : PrimeField.LawfulFp) =
      (Fp.value base : PrimeField.LawfulFp) ^ Fp.bytesValueArray exponent *
        (Fp.montgomeryRadix : PrimeField.LawfulFp) :=
  Fp.lawful_montgomeryPowBytes hbase exponent

example {base : Fp.Limbs} (hbase : Fp.Canonical base)
    (exponent : ByteArray) :
    Fp.Canonical (Fp.montgomeryPowDecodedBytes base exponent) :=
  Fp.canonical_montgomeryPowDecodedBytes hbase exponent

example {base : Fp.Limbs} (hbase : Fp.Canonical base)
    (exponent : ByteArray) :
    (Fp.value (Fp.montgomeryPowDecodedBytes base exponent) :
      PrimeField.LawfulFp) =
      (Fp.value base : PrimeField.LawfulFp) ^ Fp.bytesValueArray exponent :=
  Fp.lawful_montgomeryPowDecodedBytes hbase exponent

example {baseM acc : Fp.Limbs} (hbaseM : Fp.Canonical baseM)
    (hacc : Fp.Canonical acc) (bit : Bool) :
    Fp.Canonical (Fp.montgomeryBitStep baseM acc bit) :=
  Fp.canonical_montgomeryBitStep hbaseM hacc bit

example {baseM acc : Fp.Limbs} (hbaseM : Fp.Canonical baseM)
    (hacc : Fp.Canonical acc) (bits : List Bool) :
    Fp.Canonical (Fp.foldMontgomeryBits baseM acc bits) :=
  Fp.canonical_foldMontgomeryBits hbaseM hacc bits

example {base : Fp.Limbs} (hbase : Fp.Canonical base)
    (exponent : List UInt8) :
    Fp.Canonical (Fp.montgomeryPow base exponent) :=
  Fp.canonical_montgomeryPow hbase exponent

example (base : Fp.Limbs) :
    Fp.montgomeryPow base [2] =
      Fp.montMul2 (Fp.montgomeryEncode base) (Fp.montgomeryEncode base) :=
  rfl

example (base : Fp.Limbs) :
    Fp.montgomeryPow base [3] =
      Fp.montMul2
        (Fp.montMul2 (Fp.montgomeryEncode base) (Fp.montgomeryEncode base))
        (Fp.montgomeryEncode base) :=
  rfl

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.binaryValue_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.binaryValue_append

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.binaryValue_reverse_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp.binaryValue_reverse_bits

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.binaryValue_significantByteBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp.binaryValue_significantByteBits

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.bits_length_le_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.bits_length_le_eight

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.length_byteBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.length_byteBits

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.binaryValue_replicate_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.binaryValue_replicate_false

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.binaryValue_byteBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp.binaryValue_byteBits

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.length_flatMap_byteBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.length_flatMap_byteBits

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.binaryValue_flatMap_byteBits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.binaryValue_flatMap_byteBits

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.bytesValue_dropLeadingZeroBytes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.bytesValue_dropLeadingZeroBytes

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.binaryValue_exponentBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.binaryValue_exponentBits

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.reverse_bits_eq_true_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp.reverse_bits_eq_true_cons

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.dropLeadingZeroBytes_head_ne_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.dropLeadingZeroBytes_head_ne_zero

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.scanExponent_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.scanExponent_value

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_montgomeryBitStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.canonical_montgomeryBitStep

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_foldMontgomeryBits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.canonical_foldMontgomeryBits

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_montgomeryPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.canonical_montgomeryPow

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.scanExponent_none_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp.scanExponent_none_value

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.mul_mul_inv_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.mul_mul_inv_scale

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_montgomeryBitStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.lawful_montgomeryBitStep

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_foldMontgomeryBits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.lawful_foldMontgomeryBits

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_foldMontgomeryBits_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.lawful_foldMontgomeryBits_same

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_foldMontgomeryBits_from_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.lawful_foldMontgomeryBits_from_base

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_montgomeryPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.lawful_montgomeryPow

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_montgomeryPowDecoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.canonical_montgomeryPowDecoded

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_montgomeryPowDecoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.lawful_montgomeryPowDecoded

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_montgomeryPowBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.canonical_montgomeryPowBytes

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_montgomeryPowBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.lawful_montgomeryPowBytes

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_montgomeryPowDecodedBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.canonical_montgomeryPowDecodedBytes

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_montgomeryPowDecodedBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.lawful_montgomeryPowDecodedBytes

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.sourceTopBit_eq_highestSetBit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.sourceTopBit_eq_highestSetBit

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.sourceFirstRemainingBits_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.sourceFirstRemainingBits_eq

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.sourceLaterByteBits_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.sourceLaterByteBits_eq

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.sourceScanExponent_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.sourceScanExponent_eq

end Checks.Bls12381FpMontgomeryPow
