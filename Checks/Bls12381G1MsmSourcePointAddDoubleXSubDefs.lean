import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDefs

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check pointAddDoubleXSubLeftBody_length
#check pointAddDoubleXSubRightTail_length
#check hoist_pointAddDoubleXSubLeftBody
#check hoist_pointAddDoubleXSubBody

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.hoist_pointAddDoubleXSubBody' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms hoist_pointAddDoubleXSubBody
