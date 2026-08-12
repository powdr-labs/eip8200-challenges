import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2SubBody

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

#check exec_fp2SubStmt3
#check exec_fp2SubC1Stores
#check exec_fp2SubBody

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.exec_fp2SubBody' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_fp2SubBody
