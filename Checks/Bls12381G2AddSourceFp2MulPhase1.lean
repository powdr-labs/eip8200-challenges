import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulPhase1

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

#check exec_fp2MulStmt3
#check exec_fp2MulV1Stores

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.exec_fp2MulStmt3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_fp2MulStmt3
