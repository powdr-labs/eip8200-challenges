import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddYSum

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_pointAddYSumArgs

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_pointAddYSumArgs' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms step_pointAddYSumArgs
