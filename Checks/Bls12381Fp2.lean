import Challenge.Bls12381.ProofSupport.Fp2

set_option warningAsError true

namespace Checks.Bls12381Fp2

open Challenge.Bls12381.ProofSupport

example (a : EvmSemantics.Crypto.Bls12381.Fp2) :
    LawfulFp2.toWire (LawfulFp2.ofWire a) = a :=
  LawfulFp2.toWire_ofWire a

example (a : LawfulFp2.Carrier) (ha : a ≠ 0) : a * a⁻¹ = 1 :=
  LawfulFp2.mul_inv_cancel a ha

#print axioms LawfulFp2.toWire_ofWire
#print axioms LawfulFp2.mul_inv_cancel

example
    (invert : Fp.Limbs → Fp.Limbs)
    (a : Fp2.Repr)
    (hinvert : PrimeField.finEquiv (Fp.toField (invert
      (Challenge.Bls12381.ProofSupport.Fp2.norm a))) =
      (PrimeField.finEquiv (Fp.toField
        (Challenge.Bls12381.ProofSupport.Fp2.norm a)))⁻¹) :
    Fp2.toLawful (Fp2.invWith invert a) = (Fp2.toLawful a)⁻¹ :=
  Fp2.toLawful_invWith invert a hinvert

#print axioms Fp2.toLawful_invWith

example : Challenge.Bls12381.ProofSupport.Fp2.toField
    Challenge.Bls12381.ProofSupport.Fp2.zero = 0 :=
  Challenge.Bls12381.ProofSupport.Fp2.toField_zero

example : Challenge.Bls12381.ProofSupport.Fp2.toField
    Challenge.Bls12381.ProofSupport.Fp2.one = 1 :=
  Challenge.Bls12381.ProofSupport.Fp2.toField_one

example (a : Challenge.Bls12381.ProofSupport.Fp2.Repr) :
    Challenge.Bls12381.ProofSupport.Fp2.toField
        (Challenge.Bls12381.ProofSupport.Fp2.conj a) =
      _root_.Fp2.conj (Challenge.Bls12381.ProofSupport.Fp2.toField a) :=
  Challenge.Bls12381.ProofSupport.Fp2.toField_conj a

example
    (invert : Challenge.Bls12381.ProofSupport.Fp.Limbs →
      Challenge.Bls12381.ProofSupport.Fp.Limbs)
    (a : Challenge.Bls12381.ProofSupport.Fp2.Repr)
    (hinvert : Challenge.Bls12381.ProofSupport.Fp.toField
        (invert (Challenge.Bls12381.ProofSupport.Fp2.norm a)) =
      (Challenge.Bls12381.ProofSupport.Fp.toField
        (Challenge.Bls12381.ProofSupport.Fp2.norm a))⁻¹) :
    Challenge.Bls12381.ProofSupport.Fp2.toField
        (Challenge.Bls12381.ProofSupport.Fp2.invWith invert a) =
      _root_.Fp2.inv (Challenge.Bls12381.ProofSupport.Fp2.toField a) :=
  Challenge.Bls12381.ProofSupport.Fp2.toField_invWith invert a hinvert

#print axioms Challenge.Bls12381.ProofSupport.Fp2.toField_conj
#print axioms Challenge.Bls12381.ProofSupport.Fp2.toField_invWith

end Checks.Bls12381Fp2
