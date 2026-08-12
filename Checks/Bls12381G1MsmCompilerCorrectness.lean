import Challenge.Bls12381G1Msm.Reference.Proofs.CompilerCorrectness

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.CompilerCorrectness

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.CompilerCorrectness.referenceBackendBlock_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceBackendBlock_correct
