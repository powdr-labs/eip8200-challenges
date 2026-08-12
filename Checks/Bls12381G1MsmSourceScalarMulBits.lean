import Challenge.Bls12381G1Msm.Reference.Proofs.SourceScalarMulBits

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check scalarMulInitialBit_eq
#check scalarMulNextBit_succ
#check scalarMulBit_ne_zero
#check scalarMulNextBit_zero

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.scalarMulNextBit_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms scalarMulNextBit_succ
