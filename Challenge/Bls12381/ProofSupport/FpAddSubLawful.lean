import Challenge.Bls12381.ProofSupport.FpAddSub
import Challenge.Bls12381.ProofSupport.PrimeField

set_option warningAsError true

/-! # Lawful-field refinement of source-faithful Fp add/sub/neg -/

namespace Challenge.Bls12381.ProofSupport.Fp

open PrimeField

theorem toLawful_addSource {a b : Limbs} (ha : Canonical a)
    (hb : Canonical b) :
    finEquiv (toField (addSource a b)) =
      finEquiv (toField a) + finEquiv (toField b) := by
  rw [toField_addSource ha hb, map_add]

theorem toLawful_subSource {a b : Limbs} (ha : Canonical a)
    (hb : Canonical b) :
    finEquiv (toField (subSource a b)) =
      finEquiv (toField a) - finEquiv (toField b) := by
  rw [toField_subSource ha hb, map_sub]

theorem toLawful_negSource {a : Limbs} (ha : Canonical a) :
    finEquiv (toField (negSource a)) = -finEquiv (toField a) := by
  rw [toField_negSource ha, map_neg]

end Challenge.Bls12381.ProofSupport.Fp
