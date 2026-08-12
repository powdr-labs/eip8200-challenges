import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpAddCall

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_fpAdd_of_args

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_fpAdd_of_args' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_fpAdd_of_args

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_fpAdd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_fpAdd
