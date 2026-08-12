import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulInputStores

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check exec_fpMulInputStores

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.exec_fpMulInputStores' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_fpMulInputStores
