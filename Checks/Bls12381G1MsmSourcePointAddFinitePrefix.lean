import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddFinitePrefix

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_pointAddFinitePrefix

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_pointAddFinitePrefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_pointAddFinitePrefix
