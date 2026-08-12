import Challenge.Bls12381G1Msm.Reference.Proofs.SourceScalarMulLoop

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check ScalarMulTrace
#check step_scalarMulLoop
#check step_scalarMulFor

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_scalarMulFor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_scalarMulFor
