import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulProduct

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_fpMulProduct

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_fpMulProduct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_fpMulProduct
