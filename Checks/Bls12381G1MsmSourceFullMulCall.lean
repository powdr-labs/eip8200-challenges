import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFullMulCall

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_fullMul

#check step_fullMul_of_args

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_fullMul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_fullMul

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_fullMul_of_args' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_fullMul_of_args
