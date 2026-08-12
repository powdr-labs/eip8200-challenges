import Challenge.Bls12381.ProofSupport.Fp2SqrtRefinement

set_option warningAsError true

namespace Checks.Bls12381Fp2SqrtRefinement

open Challenge.Bls12381.ProofSupport

example :
    (Fp.value Fp2.invTwo : LawfulFp2.Base) = Fp2.lawfulInvTwo :=
  Fp2.invTwo_refines_lawful

example {a : Fp.Limbs} {b : LawfulFp2.Base}
    (h : Fp2.SqrtCellRel a b) :
    Fp2.SqrtCellRel (Fp.sqrtCanonical a) (Fp2.lawfulSqrt b) :=
  Fp2.sqrtCell_refines_lawful h

example {a : Fp2.Repr} (ha : Fp2.Canonical a) :
    (Fp2.sqrtSource a).exists_ =
        (Fp2.SqrtProgram.run Fp2.lawfulSqrtOps (Fp2.toLawful a)).exists_ ∧
      Fp2.SqrtPairRel (Fp2.sqrtSource a).root
        (Fp2.SqrtProgram.run Fp2.lawfulSqrtOps (Fp2.toLawful a)).root :=
  Fp2.sqrtSource_refines_lawful ha

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.sqrtSourceOps_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.sqrtSourceOps_refines

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.sqrtSource_refines_lawful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Fp2.sqrtSource_refines_lawful

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.invTwo_refines_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.invTwo_refines_lawful

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.sqrtCell_refines_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.sqrtCell_refines_lawful

end Checks.Bls12381Fp2SqrtRefinement
