import Challenge.Bls12381G1Msm.Reference.Proofs.SourceOnCurveBody

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_onCurveBody

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_onCurveBody' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_onCurveBody
