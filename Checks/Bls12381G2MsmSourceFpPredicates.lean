import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpPredicates

set_option warningAsError true

open Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

#check eval_fpGeModulus
#check eval_fpZero
#check conv_fpGeModulusValue
#check conv_fpZeroValue

/-- info: 'Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics.eval_fpGeModulus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eval_fpGeModulus

/-- info: 'Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics.eval_fpZero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eval_fpZero
