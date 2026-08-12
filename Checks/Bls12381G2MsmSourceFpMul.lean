import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpMulExec

set_option warningAsError true

open Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

#check eval_fpMul

/-- info: 'Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics.eval_fpMul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eval_fpMul
