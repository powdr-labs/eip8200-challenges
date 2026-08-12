import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFullMulValue

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check conv_fullMulValue

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.conv_fullMulValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms conv_fullMulValue
