import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFullMulFinal

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check exec_fullMulFinal

#check fullMulHighValue_eq

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.fullMulHighValue_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fullMulHighValue_eq

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.exec_fullMulFinal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exec_fullMulFinal
