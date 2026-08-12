import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2SubExec

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

#check eval_fp2Sub

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.eval_fp2Sub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eval_fp2Sub
