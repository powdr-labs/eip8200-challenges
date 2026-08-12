import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubLeftEnvLookup

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check pointAddDoubleXSubLeftEnv_hi
#check pointAddDoubleXSubLeftEnv_lo

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.pointAddDoubleXSubLeftEnv_hi' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pointAddDoubleXSubLeftEnv_hi
