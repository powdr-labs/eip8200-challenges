import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleInvCall

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check exec_pointAddDoubleInvCall

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.exec_pointAddDoubleInvCall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_pointAddDoubleInvCall
