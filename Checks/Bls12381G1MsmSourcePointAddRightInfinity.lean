import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddRightInfinity

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_pointAddRightInfinity

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_pointAddRightInfinity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_pointAddRightInfinity
