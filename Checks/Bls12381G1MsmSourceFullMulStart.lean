import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFullMulDefs

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check fullMulBody_length

#check hoist_fullMulBody

#check lookup_fullMul

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.fullMulBody_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms fullMulBody_length

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.hoist_fullMulBody' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hoist_fullMulBody

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.lookup_fullMul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lookup_fullMul
