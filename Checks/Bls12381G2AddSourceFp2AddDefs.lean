import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddDefs

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

example : fp2AddBody.length = 6 := by decide
#check lookup_fp2Add
#check fp2AddC0
#check fp2AddC1
#check fp2AddFinalState

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.lookup_fp2Add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lookup_fp2Add
