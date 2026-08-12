import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulDefs

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

example : fp2MulBody.length = 24 := by decide
#check lookup_fp2Mul
#check fp2MulStmt23

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.lookup_fp2Mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lookup_fp2Mul
