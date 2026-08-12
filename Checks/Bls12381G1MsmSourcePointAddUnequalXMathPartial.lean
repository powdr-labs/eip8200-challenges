import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubLeftMath
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubRightRepair

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check pointAddUnequalX3Limbs_eq
#check pointAddUnequalXSubLeftResult_eq
#check pointAddUnequalXSubRightResultLimbs_eq

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.pointAddUnequalX3Limbs_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pointAddUnequalX3Limbs_eq

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.pointAddUnequalXSubLeftResult_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pointAddUnequalXSubLeftResult_eq

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.pointAddUnequalXSubRightResultLimbs_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pointAddUnequalXSubRightResultLimbs_eq
