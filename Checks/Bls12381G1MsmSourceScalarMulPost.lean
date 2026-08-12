import Challenge.Bls12381G1Msm.Reference.Proofs.SourceScalarMulPost

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check scalarMulLoopEnv
#check step_scalarMulLoopCondition
#check step_scalarMulLoopPost

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_scalarMulLoopPost' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms step_scalarMulLoopPost
