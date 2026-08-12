import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpCore

set_option warningAsError true

open Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

#check eval_fpValid
#check eval_fpEq
#check eval_fullMul
#check eval_storeFp
#check eval_storeModulus
#check conv_fpAddValue
#check conv_fpSubValue

/-- info: 'Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics.eval_fullMul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eval_fullMul
