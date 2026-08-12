import Challenge.Bls12381G2Add
import Challenge.Bls12381.Vectors

set_option warningAsError true

open Challenge.Bls12381.ProofSupport

example : Challenge.Bls12381G2Add.inputBytes = 512 := rfl

example {input output : ByteArray} :
    Challenge.Bls12381G2Add.spec input = some output ↔
      input.size = Challenge.Bls12381G2Add.inputBytes ∧
      ∃ left right,
        Codec.decodeG2 input 0 = some left ∧
        Codec.decodeG2 input Codec.g2Bytes = some right ∧
        output = Codec.encodeG2 (G2Affine.toWire
          (G2Affine.add (G2Affine.ofWire left) (G2Affine.ofWire right))) :=
  Challenge.Bls12381G2Add.spec_eq_some_iff

example {input : ByteArray} :
    Challenge.Bls12381G2Add.spec input = none ↔
      input.size ≠ Challenge.Bls12381G2Add.inputBytes ∨
      Codec.decodeG2 input 0 = none ∨
      Codec.decodeG2 input Codec.g2Bytes = none :=
  Challenge.Bls12381G2Add.spec_eq_none_iff

#guard Challenge.Bls12381G2Add.spec
    Challenge.Bls12381.Vectors.g2Add.input =
  some Challenge.Bls12381.Vectors.g2Add.expected

#guard Challenge.Bls12381G2Add.spec
    Challenge.Bls12381.Vectors.g2AddNonSubgroup.input =
  some Challenge.Bls12381.Vectors.g2AddNonSubgroup.expected

#guard Challenge.Bls12381G2Add.spec (Challenge.Bls12381.Vectors.zeros 511) = none
#guard Challenge.Bls12381G2Add.spec (Challenge.Bls12381.Vectors.zeros 513) = none

private def offCurveInput : ByteArray :=
  Codec.encodeG2 (.affine 1 1) ++ Challenge.Bls12381.Vectors.zeros Codec.g2Bytes

#guard Challenge.Bls12381G2Add.spec offCurveInput = none

/-! The local specification theorems may use only Lean's standard quotient and
propositional extensionality axioms plus classical choice. -/

/-- info: 'Challenge.Bls12381G2Add.spec_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381G2Add.spec_eq_some_iff

/-- info: 'Challenge.Bls12381G2Add.spec_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381G2Add.spec_eq_none_iff

/-- info: 'Challenge.Bls12381G2Add.spec_invalid_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381G2Add.spec_invalid_length

/-- info: 'Challenge.Bls12381G2Add.spec_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381G2Add.spec_success

