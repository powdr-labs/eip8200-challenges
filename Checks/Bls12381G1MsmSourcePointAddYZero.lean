import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddYZero

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_pointAddYZero

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_pointAddYZero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_pointAddYZero

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.pointAddYZeroValue_eq_one_iff' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms pointAddYZeroValue_eq_one_iff

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.pointAddYZeroValue_eq_zero_iff' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms pointAddYZeroValue_eq_zero_iff
