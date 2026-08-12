import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFullMulMiddle

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check exec_fullMulMiddle

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.exec_fullMulMiddle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exec_fullMulMiddle
