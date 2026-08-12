import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulProductStores

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check exec_fpMulProductStores

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.exec_fpMulProductStores' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_fpMulProductStores
