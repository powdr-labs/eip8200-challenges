import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpAddRefinement

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check fpAddResult_toSource

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.fpAddResult_eq_shared' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms fpAddResult_eq_shared

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.fpAddResult_toSource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpAddResult_toSource
