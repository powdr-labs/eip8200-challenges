import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleDeltaBridge

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_pointAddDoubleDeltaInitAndStmt

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_pointAddDoubleDeltaInitAndStmt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_pointAddDoubleDeltaInitAndStmt
