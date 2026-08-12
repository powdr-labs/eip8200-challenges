import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpAdd

set_option warningAsError true

open Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

#check eval_fpAdd
#check conv_fpAddValue

/-- info: 'Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics.eval_fpAdd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eval_fpAdd
