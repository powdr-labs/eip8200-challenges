import Challenge.Bls12381.ProofSupport.FpMontgomeryPowInvariant

set_option warningAsError true

/-! # Lawful-field refinement of source Montgomery exponentiation -/

namespace Challenge.Bls12381.ProofSupport.Fp

open PrimeField

theorem lawful_foldMontgomeryBits_same {baseM : Limbs}
    (hcanonical : Canonical baseM) {baseValue : LawfulFp}
    (hvalue : (value baseM : LawfulFp) =
      baseValue * (montgomeryRadix : LawfulFp))
    (bits : List Bool) :
    (value (foldMontgomeryBits baseM baseM bits) : LawfulFp) =
      baseValue ^ (2 ^ bits.length + binaryValue bits) *
        (montgomeryRadix : LawfulFp) := by
  have hvalueOne : (value baseM : LawfulFp) =
      baseValue ^ 1 * (montgomeryRadix : LawfulFp) := by
    simpa only [pow_one] using hvalue
  have hfold := @lawful_foldMontgomeryBits baseM baseM hcanonical hcanonical
    baseValue 1 hvalue hvalueOne bits
  simpa only [one_mul] using hfold

/-- Specialize the fold invariant to the source initialization `rM := aM`,
where the consumed prefix is the first significant one bit. -/
theorem lawful_foldMontgomeryBits_from_base {base : Limbs}
    (hbase : Canonical base) (bits : List Bool) :
    (value (foldMontgomeryBits (montgomeryEncode base)
      (montgomeryEncode base) bits) : LawfulFp) =
      (value base : LawfulFp) ^ (2 ^ bits.length + binaryValue bits) *
        (montgomeryRadix : LawfulFp) := by
  have hcanonical : Canonical (montgomeryEncode base) :=
    canonical_montgomeryEncode hbase
  have hvalue : (value (montgomeryEncode base) : LawfulFp) =
      (value base : LawfulFp) * (montgomeryRadix : LawfulFp) :=
    lawful_montgomeryEncode hbase
  exact lawful_foldMontgomeryBits_same hcanonical hvalue bits

/-- The complete source loop returns `base^exponent` in Montgomery form. -/
theorem lawful_montgomeryPow {base : Limbs} (hbase : Canonical base)
    (exponent : List UInt8) :
    (value (montgomeryPow base exponent) : LawfulFp) =
      (value base : LawfulFp) ^ bytesValue exponent *
        (montgomeryRadix : LawfulFp) := by
  unfold montgomeryPow
  rw [sourceScanExponent_eq]
  generalize hscan : scanExponent exponent = scanned
  cases scanned with
  | none =>
      rw [lawful_montgomeryOne, scanExponent_none_value hscan, pow_zero,
        one_mul]
  | some scan =>
      rcases scan with ⟨first, bits⟩
      rw [lawful_foldMontgomeryBits_from_base hbase]
      rw [scanExponent_value hscan]

/-- Decode the completed Montgomery loop to an ordinary canonical wire value. -/
def montgomeryPowDecoded (base : Limbs) (exponent : List UInt8) : Limbs :=
  montgomeryDecode (montgomeryPow base exponent)

theorem canonical_montgomeryPowDecoded {base : Limbs}
    (hbase : Canonical base) (exponent : List UInt8) :
    Canonical (montgomeryPowDecoded base exponent) :=
  canonical_montgomeryDecode (canonical_montgomeryPow hbase exponent)

theorem lawful_montgomeryPowDecoded {base : Limbs}
    (hbase : Canonical base) (exponent : List UInt8) :
    (value (montgomeryPowDecoded base exponent) : LawfulFp) =
      (value base : LawfulFp) ^ bytesValue exponent := by
  rw [montgomeryPowDecoded,
    lawful_montgomeryDecode (canonical_montgomeryPow hbase exponent),
    lawful_montgomeryPow hbase exponent, mul_assoc,
    mul_inv_cancel₀ lawful_montgomeryRadix_ne_zero, mul_one]

/-! Thin adapters for the byte-array input used by the EVM boundary. -/

def bytesValueArray (exponent : ByteArray) : Nat :=
  bytesValue exponent.toList

def montgomeryPowBytes (base : Limbs) (exponent : ByteArray) : Limbs :=
  montgomeryPow base exponent.toList

def montgomeryPowDecodedBytes (base : Limbs) (exponent : ByteArray) : Limbs :=
  montgomeryPowDecoded base exponent.toList

theorem canonical_montgomeryPowBytes {base : Limbs}
    (hbase : Canonical base) (exponent : ByteArray) :
    Canonical (montgomeryPowBytes base exponent) :=
  canonical_montgomeryPow hbase exponent.toList

theorem lawful_montgomeryPowBytes {base : Limbs}
    (hbase : Canonical base) (exponent : ByteArray) :
    (value (montgomeryPowBytes base exponent) : LawfulFp) =
      (value base : LawfulFp) ^ bytesValueArray exponent *
        (montgomeryRadix : LawfulFp) :=
  lawful_montgomeryPow hbase exponent.toList

theorem canonical_montgomeryPowDecodedBytes {base : Limbs}
    (hbase : Canonical base) (exponent : ByteArray) :
    Canonical (montgomeryPowDecodedBytes base exponent) :=
  canonical_montgomeryPowDecoded hbase exponent.toList

theorem lawful_montgomeryPowDecodedBytes {base : Limbs}
    (hbase : Canonical base) (exponent : ByteArray) :
    (value (montgomeryPowDecodedBytes base exponent) : LawfulFp) =
      (value base : LawfulFp) ^ bytesValueArray exponent :=
  lawful_montgomeryPowDecoded hbase exponent.toList

end Challenge.Bls12381.ProofSupport.Fp
