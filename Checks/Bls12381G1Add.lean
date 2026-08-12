import Challenge.Bls12381G1Add
import Challenge.Bls12381.Vectors
import Challenge.Bls12381G1Add.Reference.Proofs.FinalCorrectness
set_option warningAsError true

open Challenge.Bls12381.ProofSupport
open Challenge.Bls12381G1Add
open Challenge.Bls12381G1Add.Reference.Proofs.FinalCorrectness

example : Challenge.Bls12381G1Add.inputBytes = 256 := rfl

example {input output : ByteArray} :
    Challenge.Bls12381G1Add.spec input = some output ↔
      input.size = Challenge.Bls12381G1Add.inputBytes ∧
      ∃ left right,
        Codec.decodeG1 input 0 = some left ∧
        Codec.decodeG1 input Codec.g1Bytes = some right ∧
        output = Codec.encodeG1 (G1Affine.toWire
          (G1Affine.add (G1Affine.ofWire left) (G1Affine.ofWire right))) :=
  Challenge.Bls12381G1Add.spec_eq_some_iff

example {input : ByteArray} :
    Challenge.Bls12381G1Add.spec input = none ↔
      input.size ≠ Challenge.Bls12381G1Add.inputBytes ∨
      Codec.decodeG1 input 0 = none ∨
      Codec.decodeG1 input Codec.g1Bytes = none :=
  Challenge.Bls12381G1Add.spec_eq_none_iff

#guard Challenge.Bls12381G1Add.spec
    Challenge.Bls12381.Vectors.g1Add.input =
  some Challenge.Bls12381.Vectors.g1Add.expected

#guard Challenge.Bls12381G1Add.spec
    Challenge.Bls12381.Vectors.g1AddNonSubgroup.input =
  some Challenge.Bls12381.Vectors.g1AddNonSubgroup.expected

#guard Challenge.Bls12381G1Add.spec (Challenge.Bls12381.Vectors.zeros 255) = none
#guard Challenge.Bls12381G1Add.spec (Challenge.Bls12381.Vectors.zeros 257) = none

private def offCurveInput : ByteArray :=
  Codec.encodeG1 (.affine 1 1) ++ Challenge.Bls12381.Vectors.zeros Codec.g1Bytes

#guard Challenge.Bls12381G1Add.spec offCurveInput = none

/-- info: 'Challenge.Bls12381G1Add.spec_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381G1Add.spec_eq_some_iff

/-- info: 'Challenge.Bls12381G1Add.spec_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381G1Add.spec_eq_none_iff

/-- info: 'Challenge.Bls12381G1Add.spec_invalid_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381G1Add.spec_invalid_length

/-- info: 'Challenge.Bls12381G1Add.spec_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381G1Add.spec_success

/--
info: 'Challenge.Bls12381G1Add.correct_of_schedule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Bls12381G1Add.correct_of_schedule

/-- info: 'Challenge.Bls12381G1Add.deployAddress_not_precompile' does not depend on any axioms -/
#guard_msgs in
#print axioms Challenge.Bls12381G1Add.deployAddress_not_precompile

#check gasSchedule
#check reference_correctWithSchedule
#check reference_correct

example : CorrectWithSchedule referenceBytecode gasSchedule :=
  reference_correctWithSchedule

example : Correct referenceBytecode := reference_correct

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.FinalCorrectness.reference_correctWithSchedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reference_correctWithSchedule

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.FinalCorrectness.reference_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reference_correct
