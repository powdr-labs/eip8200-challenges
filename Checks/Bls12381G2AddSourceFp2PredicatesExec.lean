import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2PredicatesExec

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.eval_fp2Valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eval_fp2Valid

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.eval_fp2Zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eval_fp2Zero

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.eval_fp2Eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eval_fp2Eq
