import Challenge.Bls12381G1Msm.Reference.Proofs.SourceScalarMulCalls

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check step_scalarMulDouble
#check step_scalarMulAddSkip
#check step_scalarMulAddTaken
#check step_scalarMulLoopBodySkip
#check step_scalarMulLoopBodyTaken

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_scalarMulLoopBodyTaken' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms step_scalarMulLoopBodyTaken
