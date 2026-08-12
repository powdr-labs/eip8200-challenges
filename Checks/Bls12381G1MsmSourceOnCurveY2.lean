import Challenge.Bls12381G1Msm.Reference.Proofs.SourceOnCurveY2

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_onCurveY2

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_onCurveY2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_onCurveY2
