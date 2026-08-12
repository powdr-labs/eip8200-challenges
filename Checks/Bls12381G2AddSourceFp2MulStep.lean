import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulStep
set_option warningAsError true
open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
#check step_fp2MulBodyStmts
#check step_fp2MulBody
/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.step_fp2MulBody' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_fp2MulBody
