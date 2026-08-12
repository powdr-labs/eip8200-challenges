import Challenge.Bls12381G1Msm.Reference.Proofs.SourceOnCurveX3

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_onCurveX3

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_onCurveX3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_onCurveX3
