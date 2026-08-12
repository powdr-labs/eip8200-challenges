import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulExec

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_fpMul

#check step_fpMul_of_args

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_fpMul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_fpMul

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_fpMul_of_args' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_fpMul_of_args

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.fpMulBodyResultEnv_hi' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulBodyResultEnv_hi

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.fpMulBodyResultEnv_lo' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulBodyResultEnv_lo
