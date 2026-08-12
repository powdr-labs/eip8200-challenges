import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2SubDefs

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

example : fp2SubBody.length = 6 := by decide
#check lookup_fp2Sub
#check fp2SubC0
#check fp2SubC1
#check fp2SubFinalState

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.lookup_fp2Sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lookup_fp2Sub
