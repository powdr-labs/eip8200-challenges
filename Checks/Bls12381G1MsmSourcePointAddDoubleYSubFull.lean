import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleYSubFull

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_pointAddDoubleYSubGeneric

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_pointAddDoubleYSubGeneric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_pointAddDoubleYSubGeneric
