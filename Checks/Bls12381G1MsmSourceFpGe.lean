import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpGe

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.eval_fpGeModulus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eval_fpGeModulus

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.conv_fpGeModulusValue' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms conv_fpGeModulusValue
