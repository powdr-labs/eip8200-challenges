import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulOutput

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check exec_fpMulOutput

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.exec_fpMulOutput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exec_fpMulOutput
