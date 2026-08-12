import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleInv

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check exec_pointAddDoubleInvPrefix

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.exec_pointAddDoubleInvPrefix' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_pointAddDoubleInvPrefix
