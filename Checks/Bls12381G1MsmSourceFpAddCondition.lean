import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpAddCondition

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.eval_fpAddCondition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eval_fpAddCondition
