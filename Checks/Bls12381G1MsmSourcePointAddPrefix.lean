import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddPrefix

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_pointAddPrefix

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_pointAddPrefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_pointAddPrefix
