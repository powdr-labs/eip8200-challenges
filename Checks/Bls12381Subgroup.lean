import Challenge.Bls12381.ProofSupport.Subgroup

set_option warningAsError true

namespace Checks.Bls12381Subgroup

open Challenge.Bls12381.ProofSupport
open EvmSemantics.Crypto.Bls12381

example (point : G1Affine.Point) :
    Subgroup.g1Affine point = true ↔
      ScalarMul.g1 N point = G1Affine.infinity :=
  Subgroup.g1Affine_eq_true_iff point

example (point : G2Affine.Point) :
    Subgroup.g2Affine point = true ↔
      ScalarMul.g2 N point = G2Affine.infinity :=
  Subgroup.g2Affine_eq_true_iff point

example (point : Point) :
    Subgroup.g1 point = true ↔
      ScalarMul.g1 N (G1Affine.ofWire point) = G1Affine.infinity :=
  Subgroup.g1_eq_true_iff point

example (point : G2Point) :
    Subgroup.g2 point = true ↔
      ScalarMul.g2 N (G2Affine.ofWire point) = G2Affine.infinity :=
  Subgroup.g2_eq_true_iff point

#guard Subgroup.g1 (.infinity : Point)
#guard Subgroup.g2 (.infinity : G2Point)

/--
info: 'Challenge.Bls12381.ProofSupport.Subgroup.g1Affine_eq_true_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Subgroup.g1Affine_eq_true_iff

/--
info: 'Challenge.Bls12381.ProofSupport.Subgroup.g2Affine_eq_true_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Subgroup.g2Affine_eq_true_iff

/-- info: 'Challenge.Bls12381.ProofSupport.Subgroup.g1_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Subgroup.g1_eq_true_iff

/-- info: 'Challenge.Bls12381.ProofSupport.Subgroup.g2_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Subgroup.g2_eq_true_iff

/-- info: 'Challenge.Bls12381.ProofSupport.Subgroup.g1_infinity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Subgroup.g1_infinity

/-- info: 'Challenge.Bls12381.ProofSupport.Subgroup.g2_infinity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Subgroup.g2_infinity

end Checks.Bls12381Subgroup
