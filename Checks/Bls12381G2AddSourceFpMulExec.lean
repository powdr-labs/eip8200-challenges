import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpMulExec

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

#check exec_fpMulStmt0
#check exec_fpMulStores
#check exec_fpMulCall
#check exec_fpMulBody

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.eval_fpMul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eval_fpMul

