import Challenge.Bls12381.ProofSupport.FpMontgomeryPow

set_option warningAsError true

/-! # Loop invariant for source Montgomery exponentiation -/

namespace Challenge.Bls12381.ProofSupport.Fp

open PrimeField

theorem mul_mul_inv_scale {K : Type*} [CommGroupWithZero K]
    {scale : K} (hscale : scale ≠ 0) (x y : K) :
    (x * scale) * (y * scale) * scale⁻¹ = x * y * scale := by
  calc
    (x * scale) * (y * scale) * scale⁻¹ =
        x * y * (scale * scale⁻¹) * scale := by ac_rfl
    _ = x * y * scale := by rw [mul_inv_cancel₀ hscale, mul_one]

theorem lawful_montgomeryBitStep {baseM acc : Limbs}
    (hbaseM : Canonical baseM) (hacc : Canonical acc)
    {baseValue : LawfulFp} {power : Nat}
    (hbase : (value baseM : LawfulFp) =
      baseValue * (montgomeryRadix : LawfulFp))
    (haccValue : (value acc : LawfulFp) =
      baseValue ^ power * (montgomeryRadix : LawfulFp))
    (bit : Bool) :
    (value (montgomeryBitStep baseM acc bit) : LawfulFp) =
      baseValue ^ (2 * power + bit.toNat) *
        (montgomeryRadix : LawfulFp) := by
  cases bit with
  | false =>
      rw [show montgomeryBitStep baseM acc false = montMul2 acc acc by rfl,
        lawful_montMul2 hacc hacc, haccValue,
        mul_mul_inv_scale lawful_montgomeryRadix_ne_zero]
      simp [Bool.toNat_false, two_mul, pow_add]
  | true =>
      rw [show montgomeryBitStep baseM acc true =
          montMul2 (montMul2 acc acc) baseM by rfl,
        lawful_montMul2 (canonical_montMul2 hacc hacc) hbaseM,
        lawful_montMul2 hacc hacc, haccValue,
        mul_mul_inv_scale lawful_montgomeryRadix_ne_zero, hbase,
        mul_mul_inv_scale lawful_montgomeryRadix_ne_zero]
      simp [Bool.toNat_true, two_mul, pow_add]

theorem lawful_foldMontgomeryBits {baseM acc : Limbs}
    (hbaseM : Canonical baseM) (hacc : Canonical acc)
    {baseValue : LawfulFp} {power : Nat}
    (hbase : (value baseM : LawfulFp) =
      baseValue * (montgomeryRadix : LawfulFp))
    (haccValue : (value acc : LawfulFp) =
      baseValue ^ power * (montgomeryRadix : LawfulFp))
    (bits : List Bool) :
    (value (foldMontgomeryBits baseM acc bits) : LawfulFp) =
      baseValue ^ (power * 2 ^ bits.length + binaryValue bits) *
        (montgomeryRadix : LawfulFp) := by
  induction bits generalizing acc power with
  | nil => simpa [foldMontgomeryBits, binaryValue] using haccValue
  | cons bit bits ih =>
      rw [foldMontgomeryBits]
      have hstep := lawful_montgomeryBitStep hbaseM hacc hbase haccValue bit
      rw [ih (canonical_montgomeryBitStep hbaseM hacc bit) hstep]
      congr 2
      simp only [List.length_cons, binaryValue, pow_succ]
      ring

end Challenge.Bls12381.ProofSupport.Fp
