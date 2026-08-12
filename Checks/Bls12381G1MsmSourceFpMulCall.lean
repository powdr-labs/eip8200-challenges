import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulCall

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check exec_fpMulCall

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.exec_fpMulCall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_fpMulCall
