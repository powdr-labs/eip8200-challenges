import Challenge.Bls12381G1Msm.Reference.Proofs.SourceInvalidLength

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.run_invalid_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms run_invalid_length
