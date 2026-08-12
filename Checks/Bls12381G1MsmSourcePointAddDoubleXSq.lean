import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSq

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_pointAddDoubleXSqArgs

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_pointAddDoubleXSqArgs' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms step_pointAddDoubleXSqArgs
