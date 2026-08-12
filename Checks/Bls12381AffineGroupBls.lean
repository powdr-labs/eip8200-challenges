import Challenge.Bls12381.ProofSupport.AffineGroupBls

set_option warningAsError true

namespace Checks.Bls12381AffineGroupBls

open Challenge.Bls12381.ProofSupport

example : WeierstrassCurve.IsElliptic
    (AffineGroup.mathCurve G1Affine.curve) := inferInstance

example : WeierstrassCurve.IsElliptic
    (AffineGroup.mathCurve G2Affine.curve) := inferInstance

/--
info: 'Challenge.Bls12381.ProofSupport.AffineGroupBls.g1MathCurve_discriminant_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AffineGroupBls.g1MathCurve_discriminant_ne_zero

/--
info: 'Challenge.Bls12381.ProofSupport.AffineGroupBls.g2MathCurve_discriminant_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AffineGroupBls.g2MathCurve_discriminant_ne_zero

/--
info: 'Challenge.Bls12381.ProofSupport.AffineGroupBls.g1MathCurveIsElliptic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AffineGroupBls.g1MathCurveIsElliptic

/--
info: 'Challenge.Bls12381.ProofSupport.AffineGroupBls.g2MathCurveIsElliptic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AffineGroupBls.g2MathCurveIsElliptic

end Checks.Bls12381AffineGroupBls
