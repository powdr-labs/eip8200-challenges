import Challenge.Bls12381G1Msm.Reference.Proofs.SourceOnCurveCall

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_onCurve_of_args
#check step_onCurve

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_onCurve_of_args' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_onCurve_of_args

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_onCurve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_onCurve
