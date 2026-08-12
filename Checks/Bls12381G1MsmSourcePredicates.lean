import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePredicates

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.eval_fpZero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eval_fpZero

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.eval_fpEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eval_fpEq

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_fpZero_of_args' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_fpZero_of_args

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.step_fpEq_of_args' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_fpEq_of_args

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.conv_fpValidValue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms conv_fpValidValue

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.conv_fpZeroValue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms conv_fpZeroValue

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.conv_fpEqValue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms conv_fpEqValue
