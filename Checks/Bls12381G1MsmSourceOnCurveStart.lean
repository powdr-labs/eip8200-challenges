import Challenge.Bls12381G1Msm.Reference.Proofs.SourceOnCurveDefs

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check onCurveBody_length

#check lookup_onCurve

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.onCurveBody_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms onCurveBody_length

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.lookup_onCurve' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lookup_onCurve
