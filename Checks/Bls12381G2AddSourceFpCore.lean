import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpCore

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

#check eval_fpGeModulus
#check eval_fpValid
#check eval_fpZero
#check eval_fpEq
#check eval_fpAdd
#check eval_fpSub
#check eval_fullMul
#check eval_storeFp
#check eval_storeModulus

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.conv_fpAddValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms conv_fpAddValue

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.conv_fpSubValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms conv_fpSubValue

