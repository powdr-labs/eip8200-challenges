import Challenge.Bls12381.ProofSupport.Fp2SqrtLawfulOps

set_option warningAsError true

namespace Checks.Bls12381Fp2SqrtLawfulOps

open Challenge.Bls12381.ProofSupport

example (x : LawfulFp2.Base) :
    Fp2.lawfulSqrt x =
      x ^ ((EvmSemantics.Crypto.Bls12381.p + 1) / 4) :=
  Fp2.lawfulSqrt_eq x

example : Fp2.lawfulInvTwo = (2 : LawfulFp2.Base)⁻¹ :=
  Fp2.lawfulInvTwo_eq

example {x : LawfulFp2.Base} (hx : IsSquare x) :
    Fp2.lawfulSqrt x ^ 2 = x :=
  Fp2.lawfulSqrt_square hx

example {x : LawfulFp2.Base} (hx : IsSquare x) :
    IsSquare (Fp2.lawfulSqrt x) :=
  Fp2.lawfulSqrt_isSquare hx

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.lawfulSqrt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.lawfulSqrt_eq

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.lawfulInvTwo_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.lawfulInvTwo_eq

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.lawfulSqrt_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.lawfulSqrt_square

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.lawfulSqrt_isSquare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.lawfulSqrt_isSquare

end Checks.Bls12381Fp2SqrtLawfulOps
