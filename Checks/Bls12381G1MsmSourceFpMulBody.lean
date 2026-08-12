import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulBody

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_fpMulBodyStmts

#check step_fpMulBody

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_fpMulBodyStmts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_fpMulBodyStmts

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_fpMulBody' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_fpMulBody
