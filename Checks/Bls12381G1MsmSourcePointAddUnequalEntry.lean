import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalEntry

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_pointAddXUnequal
#check step_pointAddUnequalNumeratorInit

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_pointAddXUnequal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_pointAddXUnequal
