import Challenge.Bls12381.ProofSupport.MsmSemantics

set_option warningAsError true

namespace Checks.Bls12381MsmSemantics

open Challenge.Bls12381.ProofSupport

example (terms : List MsmSemantics.G1ValidTerm) :
    AffineGroup.toMathlib G1Affine.curve
        ⟨MsmSemantics.g1Value terms, MsmSemantics.g1Value_onCurve terms⟩ =
      MsmSemantics.g1MathSum terms :=
  MsmSemantics.g1_nsmul_sum terms

example (terms : List MsmSemantics.G2ValidTerm) :
    AffineGroup.toMathlib G2Affine.curve
        ⟨MsmSemantics.g2Value terms, MsmSemantics.g2Value_onCurve terms⟩ =
      MsmSemantics.g2MathSum terms :=
  MsmSemantics.g2_nsmul_sum terms

/--
info: 'Challenge.Bls12381.ProofSupport.MsmSemantics.g1Value_onCurve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MsmSemantics.g1Value_onCurve

/--
info: 'Challenge.Bls12381.ProofSupport.MsmSemantics.g2Value_onCurve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MsmSemantics.g2Value_onCurve

/--
info: 'Challenge.Bls12381.ProofSupport.MsmSemantics.foldG1_nsmul_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MsmSemantics.foldG1_nsmul_sum

/--
info: 'Challenge.Bls12381.ProofSupport.MsmSemantics.foldG2_nsmul_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MsmSemantics.foldG2_nsmul_sum

/-- info: 'Challenge.Bls12381.ProofSupport.MsmSemantics.g1_nsmul_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MsmSemantics.g1_nsmul_sum

/-- info: 'Challenge.Bls12381.ProofSupport.MsmSemantics.g2_nsmul_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MsmSemantics.g2_nsmul_sum

end Checks.Bls12381MsmSemantics
