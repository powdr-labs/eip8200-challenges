import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulInput

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check fpMulInputState_eq_shared

#check fpMulInput_runModexp_raw

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.fpMulInputState_eq_shared' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulInputState_eq_shared

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.fpMulInput_runModexp_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulInput_runModexp_raw
