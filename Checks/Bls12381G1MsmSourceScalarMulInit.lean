import Challenge.Bls12381G1Msm.Reference.Proofs.SourceScalarMulInit

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check scalarMulInitialEnv
#check scalarMulInitState
#check scalarMulInitEnv
#check step_scalarMulInit

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_scalarMulInit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_scalarMulInit
