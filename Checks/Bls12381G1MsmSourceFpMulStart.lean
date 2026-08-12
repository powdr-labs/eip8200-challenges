import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulDefs

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check fpMulBody_length

#check lookup_fpMul

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.fpMulBody_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms fpMulBody_length

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.lookup_fpMul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lookup_fpMul
