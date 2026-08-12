import Challenge.Bls12381G2Add
import Challenge.Bls12381G2Add.Reference.Proofs.FinalCorrectness
set_option warningAsError true

open Challenge.Bls12381G2Add
open Challenge.Bls12381G2Add.Reference.Proofs.FinalCorrectness

/--
info: 'Challenge.Bls12381G2Add.correct_of_schedule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Bls12381G2Add.correct_of_schedule

/-- info: 'Challenge.Bls12381G2Add.deployAddress_not_precompile' does not depend on any axioms -/
#guard_msgs in
#print axioms Challenge.Bls12381G2Add.deployAddress_not_precompile

#check gasSchedule
#check reference_correctWithSchedule
#check reference_correct

example : CorrectWithSchedule referenceBytecode gasSchedule :=
  reference_correctWithSchedule

example : Correct referenceBytecode := reference_correct

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.FinalCorrectness.reference_correctWithSchedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reference_correctWithSchedule

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.FinalCorrectness.reference_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reference_correct
