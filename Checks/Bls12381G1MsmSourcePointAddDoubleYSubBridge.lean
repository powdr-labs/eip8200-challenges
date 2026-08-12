import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleYSubBridge

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_pointAddDoubleYSubStmt

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_pointAddDoubleYSubStmt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_pointAddDoubleYSubStmt
