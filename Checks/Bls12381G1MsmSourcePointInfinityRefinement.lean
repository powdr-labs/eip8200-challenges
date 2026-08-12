import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointInfinityRefinement

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check pointInfinityResult_eq_one_iff
#check pointInfinityResult_eq_zero_iff

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.pointInfinityResult_eq_one_iff' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms pointInfinityResult_eq_one_iff

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.pointInfinityResult_eq_zero_iff' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms pointInfinityResult_eq_zero_iff
