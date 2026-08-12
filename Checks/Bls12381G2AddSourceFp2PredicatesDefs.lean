import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2PredicatesDefs

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

example : fp2ValidBody.length = 1 := by decide
example : fp2ZeroBody.length = 1 := by decide
example : fp2EqBody.length = 1 := by decide

#check lookup_fp2Valid
#check lookup_fp2Zero
#check lookup_fp2Eq
#check fp2At_c0_hi
#check fp2At_c1_lo

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2ZeroValue_zero_or_one' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms fp2ZeroValue_zero_or_one

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2EqValue_zero_or_one' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms fp2EqValue_zero_or_one
