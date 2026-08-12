import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulProductDefs

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check fpMulProductBlock_length

#check fpMulProductStores_length

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.fpMulProductBlock_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms fpMulProductBlock_length

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.fpMulProductStores_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms fpMulProductStores_length
