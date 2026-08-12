import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleDen

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_pointAddDoubleDenArgs

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_pointAddDoubleDenArgs' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms step_pointAddDoubleDenArgs
