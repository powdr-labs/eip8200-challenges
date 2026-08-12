import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFullMulBody

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_fullMulBodyStmts

#check step_fullMulBody

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_fullMulBodyStmts' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms step_fullMulBodyStmts

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_fullMulBody' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_fullMulBody
