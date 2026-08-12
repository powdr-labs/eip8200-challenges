import Challenge.Bls12381G1Msm.Reference.Proofs.SourceOnCurveRefinement

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check onCurveResult_eq_shared
#check onCurveResult_eq_one_iff
#check onCurveResult_eq_zero_iff

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.onCurveResult_eq_shared' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms onCurveResult_eq_shared

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.onCurveResult_eq_one_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms onCurveResult_eq_one_iff

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.onCurveResult_eq_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms onCurveResult_eq_zero_iff
