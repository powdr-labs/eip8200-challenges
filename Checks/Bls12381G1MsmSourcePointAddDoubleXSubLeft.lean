import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubLeft

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check exec_pointAddDoubleXSubLeftRaw

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.exec_pointAddDoubleXSubLeftRaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_pointAddDoubleXSubLeftRaw
