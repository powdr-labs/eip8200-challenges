import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleLawful

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check pointAddDoubleDenResult_high_lt_of_canonical
#check pointAddYZeroValue_eq_zero_of_lawful_sum
#check step_pointAddDoubleEqual_lawful

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_pointAddDoubleEqual_lawful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_pointAddDoubleEqual_lawful
