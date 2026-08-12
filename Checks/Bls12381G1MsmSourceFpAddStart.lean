import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpAddStart

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.exec_fpAddStmt0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exec_fpAddStmt0

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.lookup_fpAdd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lookup_fpAdd
