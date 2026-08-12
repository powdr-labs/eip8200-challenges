import Challenge.Bls12381G1Msm.Reference.Proofs.SourceScalarMulReady

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check ScalarMulIterationReady
#check step_scalarMulIterationReady
#check ScalarMulReadySchedule
#check scalarMulTrace_of_ready

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.scalarMulTrace_of_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms scalarMulTrace_of_ready
