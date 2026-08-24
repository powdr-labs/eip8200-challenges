import Challenge.Bls12381.ProofSupport.FpInvConstants
import Mathlib.FieldTheory.Finite.Basic

set_option warningAsError true

/-! # Source-faithful BLS12-381 base-field inversion -/

namespace Challenge.Bls12381.ProofSupport.Fp

open PrimeField

/-- Exact source call `Fp.inv(a) = _modexp(a, P_MINUS_2)`. -/
def invCanonical (a : Limbs) : Limbs :=
  montgomeryPowDecoded a pMinus2Bytes

theorem canonical_invCanonical {a : Limbs} (ha : Canonical a) :
    Canonical (invCanonical a) :=
  canonical_montgomeryPowDecoded ha pMinus2Bytes

/-- The source call first refines to Fermat's fixed exponent. -/
theorem lawful_invCanonical_pow {a : Limbs} (ha : Canonical a) :
    (value (invCanonical a) : LawfulFp) =
      (value a : LawfulFp) ^
        (EvmSemantics.Crypto.Bls12381.p - 2) := by
  rw [invCanonical, lawful_montgomeryPowDecoded ha,
    bytesValue_pMinus2Bytes]

/-- Fermat inversion at the certified fixed BLS modulus, including zero. -/
theorem lawful_pow_pMinus2_eq_inv (x : LawfulFp) :
    x ^ (EvmSemantics.Crypto.Bls12381.p - 2) = x⁻¹ := by
  by_cases hzero : x = 0
  · rw [hzero, inv_zero]
    exact zero_pow (by
      norm_num [EvmSemantics.Crypto.Bls12381.p,
        EvmSemantics.Crypto.Bls12381.absU])
  · apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    have hfermat := ZMod.pow_card_sub_one_eq_one hzero
    rw [show EvmSemantics.Crypto.Bls12381.p - 2 + 1 =
        EvmSemantics.Crypto.Bls12381.p - 1 by
      norm_num [EvmSemantics.Crypto.Bls12381.p,
        EvmSemantics.Crypto.Bls12381.absU]]
    exact hfermat

/-- Lawful-field refinement of the source inversion routine. This boundary is
intentionally independent of the pinned opaque `FF.modInv`, whose API exposes
no theorem with which to state an implementation-equivalence proof. -/
theorem lawful_invCanonical {a : Limbs} (ha : Canonical a) :
    (value (invCanonical a) : LawfulFp) = (value a : LawfulFp)⁻¹ := by
  rw [lawful_invCanonical_pow ha, lawful_pow_pMinus2_eq_inv]

/-- The same refinement through the explicit wire-`Fin`/lawful-field adapter. -/
theorem toLawful_invCanonical {a : Limbs} (ha : Canonical a) :
    PrimeField.finEquiv (toField (invCanonical a)) =
      (PrimeField.finEquiv (toField a))⁻¹ := by
  simpa only [finEquiv_toField] using lawful_invCanonical ha

end Challenge.Bls12381.ProofSupport.Fp
