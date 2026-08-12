import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddBody

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

#check exec_fp2AddStmt3
#check exec_fp2AddC1Stores
#check exec_fp2AddBody

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.exec_fp2AddBody' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_fp2AddBody
