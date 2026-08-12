import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpSub

set_option warningAsError true

open Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

#check eval_fpSub
#check conv_fpSubValue

/-- info: 'Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics.eval_fpSub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eval_fpSub
