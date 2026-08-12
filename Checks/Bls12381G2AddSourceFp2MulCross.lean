import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulCross
set_option warningAsError true
open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
#check exec_fp2MulStmt15
#check exec_fp2MulCrossStores
/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.exec_fp2MulStmt15' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_fp2MulStmt15
