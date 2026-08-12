import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulRefinement

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check fpMulResult_eq_shared

#check canonical_fpMulOutput

#check fpMulOutput_toField

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.fpMulResult_eq_shared' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulResult_eq_shared

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.canonical_fpMulOutput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms canonical_fpMulOutput

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.fpMulOutput_toField' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulOutput_toField
