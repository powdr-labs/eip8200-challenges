import Challenge.Bls12381G1Msm.Reference.Proofs.SourceScalarMulBody

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_scalarMulBodyStmts
#check step_scalarMulBody
#check step_scalarMul_of_args

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_scalarMul_of_args' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms step_scalarMul_of_args
