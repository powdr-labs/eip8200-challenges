import Challenge.Bls12381.ProofSupport.FpMontgomeryMul
import Challenge.Bls12381.ProofSupport.PrimeCertificate
import Challenge.Bls12381.ProofSupport.FpPredicates

set_option warningAsError true

/-! # Lawful-field refinement of BLS12-381 `montMul2` -/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics
open EvmSemantics.Crypto.Bls12381
open PrimeField

/-- The two-word Montgomery radix is nonzero in the certified prime field. -/
theorem lawful_montgomeryRadix_ne_zero :
    (montgomeryRadix : LawfulFp) ≠ 0 := by
  intro hzero
  have hdiv : p ∣ montgomeryRadix :=
    (CharP.cast_eq_zero_iff LawfulFp p montgomeryRadix).mp hzero
  norm_num [montgomeryRadix, Challenge.EvmProof.Limbs.radix, p, absU] at hdiv

/-- Cancel a nonzero left factor without exposing a concrete reducible term to
associative-commutative normalization. -/
theorem eq_mul_inv_of_mul_eq {K : Type*} [CommGroupWithZero K]
    {base result target : K} (hbase : base ≠ 0)
    (heq : base * result = target) : result = target * base⁻¹ := by
  calc
    result = result * 1 := by rw [mul_one]
    _ = result * (base * base⁻¹) := by rw [mul_inv_cancel₀ hbase]
    _ = (base * result) * base⁻¹ := by ac_rfl
    _ = target * base⁻¹ := by rw [heq]

/-- Lawful-field interpretation of the source Montgomery multiplication. -/
theorem lawful_montMul2 {x y : Limbs}
    (hx : Canonical x) (hy : Canonical y) :
    (value (montMul2 x y) : LawfulFp) =
      (value x : LawfulFp) * (value y : LawfulFp) *
        (montgomeryRadix : LawfulFp)⁻¹ := by
  have hmod := montMul2_modEq hx hy
  have hcast : (montgomeryRadix : LawfulFp) *
        (value (montMul2 x y) : LawfulFp) =
      (value x : LawfulFp) * (value y : LawfulFp) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul]
    exact (ZMod.natCast_eq_natCast_iff _ _ p).2 hmod
  exact eq_mul_inv_of_mul_eq lawful_montgomeryRadix_ne_zero hcast

/-- The same refinement stated through the explicit wire-`Fin`/lawful-field
adapter consumed by higher tower arithmetic. -/
theorem toLawful_montMul2 {x y : Limbs}
    (hx : Canonical x) (hy : Canonical y) :
    PrimeField.finEquiv (toField (montMul2 x y)) =
      PrimeField.finEquiv (toField x) * PrimeField.finEquiv (toField y) *
        (montgomeryRadix : LawfulFp)⁻¹ := by
  simpa only [finEquiv_toField] using lawful_montMul2 hx hy

/-! ## Source conversion constants and identities -/

/-- Exact source pair for `R² mod p`. -/
def montgomeryR2 : Limbs :=
  { lo := montgomeryR2Lo, hi := montgomeryR2Hi }

@[simp] theorem value_montgomeryR2 : value montgomeryR2 = montgomeryR2Value := rfl

theorem canonical_montgomeryR2 : Canonical montgomeryR2 := by
  constructor
  · norm_num [montgomeryR2, montgomeryR2Hi,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  · rw [value_montgomeryR2, montgomeryR2_spec]
    exact Nat.mod_lt _ (by norm_num [p, absU])

/-- Exact source pair for the ordinary integer one. -/
def montgomeryOneInput : Limbs :=
  { lo := UInt256.ofNat 1, hi := UInt256.ofNat 0 }

@[simp] theorem value_montgomeryOneInput : value montgomeryOneInput = 1 := by
  norm_num [value, montgomeryOneInput,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem canonical_montgomeryOneInput : Canonical montgomeryOneInput := by
  rw [show montgomeryOneInput = pack 1 by rfl]
  exact canonical_pack (by norm_num [p, absU])

/-- The source `R²` pair represents the square of the Montgomery radix in the
lawful field. -/
theorem lawful_montgomeryR2 :
    (value montgomeryR2 : LawfulFp) =
      (montgomeryRadix : LawfulFp) * (montgomeryRadix : LawfulFp) := by
  rw [value_montgomeryR2, montgomeryR2_spec]
  rw [ZMod.natCast_mod]
  simp only [montgomeryRadix, Nat.cast_mul, Nat.cast_pow]
  ring

/-- Convert a canonical ordinary value to Montgomery form. -/
def montgomeryEncode (a : Limbs) : Limbs := montMul2 a montgomeryR2

theorem canonical_montgomeryEncode {a : Limbs} (ha : Canonical a) :
    Canonical (montgomeryEncode a) :=
  canonical_montMul2 ha canonical_montgomeryR2

theorem lawful_montgomeryEncode {a : Limbs} (ha : Canonical a) :
    (value (montgomeryEncode a) : LawfulFp) =
      (value a : LawfulFp) * (montgomeryRadix : LawfulFp) := by
  change (value (montMul2 a montgomeryR2) : LawfulFp) = _
  rw [lawful_montMul2 ha canonical_montgomeryR2, lawful_montgomeryR2]
  rw [mul_assoc, mul_assoc, mul_inv_cancel₀ lawful_montgomeryRadix_ne_zero,
    mul_one]

/-- Source initialization of Montgomery one. -/
def montgomeryOne : Limbs := montgomeryEncode montgomeryOneInput

theorem canonical_montgomeryOne : Canonical montgomeryOne :=
  canonical_montgomeryEncode canonical_montgomeryOneInput

theorem lawful_montgomeryOne :
    (value montgomeryOne : LawfulFp) = (montgomeryRadix : LawfulFp) := by
  rw [montgomeryOne, lawful_montgomeryEncode canonical_montgomeryOneInput,
    value_montgomeryOneInput, Nat.cast_one, one_mul]

/-- Convert a canonical Montgomery value back to ordinary representation. -/
def montgomeryDecode (aM : Limbs) : Limbs := montMul2 aM montgomeryOneInput

theorem canonical_montgomeryDecode {aM : Limbs} (haM : Canonical aM) :
    Canonical (montgomeryDecode aM) :=
  canonical_montMul2 haM canonical_montgomeryOneInput

theorem lawful_montgomeryDecode {aM : Limbs} (haM : Canonical aM) :
    (value (montgomeryDecode aM) : LawfulFp) =
      (value aM : LawfulFp) * (montgomeryRadix : LawfulFp)⁻¹ := by
  change (value (montMul2 aM montgomeryOneInput) : LawfulFp) = _
  rw [lawful_montMul2 haM canonical_montgomeryOneInput,
    value_montgomeryOneInput, Nat.cast_one, mul_one]

/-- Encoding and then decoding returns the original lawful field value. -/
theorem lawful_montgomeryDecode_encode {a : Limbs} (ha : Canonical a) :
    (value (montgomeryDecode (montgomeryEncode a)) : LawfulFp) =
      (value a : LawfulFp) := by
  rw [lawful_montgomeryDecode (canonical_montgomeryEncode ha),
    lawful_montgomeryEncode ha, mul_assoc,
    mul_inv_cancel₀ lawful_montgomeryRadix_ne_zero, mul_one]

theorem toField_montgomeryDecode_encode {a : Limbs} (ha : Canonical a) :
    toField (montgomeryDecode (montgomeryEncode a)) = toField a := by
  apply PrimeField.finEquiv.injective
  simpa only [finEquiv_toField] using lawful_montgomeryDecode_encode ha

/-- The full source conversion round trip returns the original canonical wire
representation, not only an equivalent field residue. -/
theorem montgomeryDecode_encode {a : Limbs} (ha : Canonical a) :
    montgomeryDecode (montgomeryEncode a) = a := by
  apply limbs_ext_of_value_eq
  have hfield := toField_montgomeryDecode_encode ha
  have hvalue := congrArg Fin.val hfield
  change value (montgomeryDecode (montgomeryEncode a)) % p =
    value a % p at hvalue
  have hdecodeCanonical := canonical_montgomeryDecode
    (canonical_montgomeryEncode ha)
  rw [Nat.mod_eq_of_lt hdecodeCanonical.2,
    Nat.mod_eq_of_lt ha.2] at hvalue
  exact hvalue

end Challenge.Bls12381.ProofSupport.Fp
