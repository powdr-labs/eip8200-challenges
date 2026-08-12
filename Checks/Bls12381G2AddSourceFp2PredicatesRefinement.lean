import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2PredicatesRefinement

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

#check fp2ValidValue_eq_one_iff_canonical
#check fp2ZeroValue_eq_one_iff_words
#check fp2EqValue_eq_one_iff_words

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2ValidValue_eq_one_iff_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fp2ValidValue_eq_one_iff_canonical

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2ZeroValue_eq_one_iff_words' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms fp2ZeroValue_eq_one_iff_words

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2EqValue_eq_one_iff_words' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms fp2EqValue_eq_one_iff_words

