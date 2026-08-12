import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointInfinityExec

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_pointInfinityBody
#check step_pointInfinity_of_args

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_pointInfinityBody' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms step_pointInfinityBody

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_pointInfinity_of_args' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_pointInfinity_of_args
