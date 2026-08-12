import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulVSum
set_option warningAsError true
open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
#check exec_fp2MulStmt18
#check exec_fp2MulVSumStores
/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.exec_fp2MulStmt18' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_fp2MulStmt18
