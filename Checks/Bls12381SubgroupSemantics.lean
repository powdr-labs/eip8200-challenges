import Challenge.Bls12381.ProofSupport.SubgroupSemantics

set_option warningAsError true

namespace Checks.Bls12381SubgroupSemantics

open Challenge.Bls12381.ProofSupport
open EvmSemantics.Crypto.Bls12381

example (point : SubgroupSemantics.G1ValidPoint) :
    Subgroup.g1Affine point.1 = true ↔
      N • AffineGroup.toMathlib G1Affine.curve point = 0 :=
  SubgroupSemantics.g1Affine_eq_true_iff_nsmul_zero point

example (point : SubgroupSemantics.G2ValidPoint) :
    Subgroup.g2Affine point.1 = true ↔
      N • AffineGroup.toMathlib G2Affine.curve point = 0 :=
  SubgroupSemantics.g2Affine_eq_true_iff_nsmul_zero point

example (point : Point) (hvalid : Codec.ValidG1 point) :
    Subgroup.g1 point = true ↔
      N • AffineGroup.toMathlib G1Affine.curve
        (SubgroupSemantics.g1PointOfWire point hvalid) = 0 :=
  SubgroupSemantics.g1_eq_true_iff_nsmul_zero point hvalid

example (point : G2Point) (hvalid : Codec.ValidG2 point) :
    Subgroup.g2 point = true ↔
      N • AffineGroup.toMathlib G2Affine.curve
        (SubgroupSemantics.g2PointOfWire point hvalid) = 0 :=
  SubgroupSemantics.g2_eq_true_iff_nsmul_zero point hvalid

/--
info: 'Challenge.Bls12381.ProofSupport.SubgroupSemantics.g1Affine_eq_true_iff_nsmul_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SubgroupSemantics.g1Affine_eq_true_iff_nsmul_zero

/--
info: 'Challenge.Bls12381.ProofSupport.SubgroupSemantics.g2Affine_eq_true_iff_nsmul_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SubgroupSemantics.g2Affine_eq_true_iff_nsmul_zero

/--
info: 'Challenge.Bls12381.ProofSupport.SubgroupSemantics.g1_eq_true_iff_nsmul_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SubgroupSemantics.g1_eq_true_iff_nsmul_zero

/--
info: 'Challenge.Bls12381.ProofSupport.SubgroupSemantics.g2_eq_true_iff_nsmul_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SubgroupSemantics.g2_eq_true_iff_nsmul_zero

end Checks.Bls12381SubgroupSemantics
