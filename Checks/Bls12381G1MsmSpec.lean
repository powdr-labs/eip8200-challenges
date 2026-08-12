import Challenge.Bls12381.Vectors
import Challenge.Bls12381G1Msm.SpecRefinement

set_option warningAsError true

namespace Checks.Bls12381G1MsmSpec

open Challenge.Bls12381
open Challenge.Bls12381.ProofSupport
open Challenge.Bls12381G1Msm

private def oneByte : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded 1 1

private def paddingInvalid : ByteArray :=
  oneByte ++ Vectors.zeros 159

private def fieldInvalid : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded
      EvmSemantics.Crypto.Bls12381.p 64 ++
    Vectors.zeros 96

private def offCurve : ByteArray :=
  Vectors.zeros 64 ++
    EvmSemantics.Data.Bytes.natToBytesPadded 1 64 ++
    Vectors.zeros 32

private def maxScalarInput : ByteArray :=
  Vectors.generatorG1 ++
    EvmSemantics.Data.Bytes.natToBytesPadded (2 ^ 256 - 1) 32

private def decodesMaxScalar : Bool :=
  match decodeTerm maxScalarInput 0 with
  | some (_, scalar) => scalar.val == 2 ^ 256 - 1
  | none => false

example (input : ByteArray) (offset : Nat) :
    Option Msm.G1WireTerm := decodeTerm input offset

example (input : ByteArray) (offset : Nat) :
    (scalarAt input offset).val = Codec.scalarWindowValue input offset := rfl

example (input : ByteArray) (offset count : Nat) :
    Option (List Msm.G1WireTerm) := decodeTerms input offset count

example (input : ByteArray) (offset : Nat) (term : Msm.G1WireTerm) :
    decodeTerm input offset = some term ↔
      Codec.decodeG1Subgroup input offset = some term.1 ∧
      Codec.decodeScalar input (offset + Codec.g1Bytes) = some term.2.val :=
  decodeTerm_eq_some_iff input offset term

example {input : ByteArray} {offset count : Nat}
    {terms : List Msm.G1WireTerm}
    (hdecode : decodeTerms input offset count = some terms) :
    terms.length = count := decodeTerms_length hdecode

example {input : ByteArray} {offset : Nat} {term : Msm.G1WireTerm}
    (hdecode : decodeTerm input offset = some term) :
    Subgroup.g1 term.1 = true := decodeTerm_subgroup hdecode

example {input output : ByteArray} : spec input = some output ↔
    input.size ≠ 0 ∧ input.size % pairBytes = 0 ∧
      ∃ terms, decodeTerms input 0 (input.size / pairBytes) = some terms ∧
        output = Codec.encodeG1 (Msm.g1Wire terms) :=
  spec_eq_some_iff

example {input : ByteArray} : spec input = none ↔
    input.size = 0 ∨ input.size % pairBytes ≠ 0 ∨
      decodeTerms input 0 (input.size / pairBytes) = none :=
  spec_eq_none_iff

#guard pairBytes = Codec.g1Bytes + Codec.scalarBytes
#guard spec ByteArray.empty = none
#guard spec (Vectors.zeros 159) = none
#guard spec (Vectors.zeros 161) = none
#guard spec (Vectors.zeros 160) = some (Vectors.zeros Codec.g1Bytes)
#guard spec (Vectors.zeros 320) = some (Vectors.zeros Codec.g1Bytes)
#guard spec paddingInvalid = none
#guard spec fieldInvalid = none
#guard spec offCurve = none
#guard spec Vectors.g1MsmNonSubgroup = none
#guard spec Vectors.g1Msm.input = some Vectors.g1Msm.expected
#guard spec Vectors.g1MsmMulti.input = some Vectors.g1MsmMulti.expected
#guard decodesMaxScalar

/-! The adapter theorems use only Lean's standard quotient and propositional
extensionality axioms plus classical choice. -/

/-- info: 'Challenge.Bls12381G1Msm.decodeTerm_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decodeTerm_eq_some_iff

/-- info: 'Challenge.Bls12381G1Msm.decodeTerm_subgroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decodeTerm_subgroup

/-- info: 'Challenge.Bls12381G1Msm.decodeTerms_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decodeTerms_length

/-- info: 'Challenge.Bls12381G1Msm.spec_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spec_eq_some_iff

/-- info: 'Challenge.Bls12381G1Msm.spec_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spec_eq_none_iff

/-- info: 'Challenge.Bls12381G1Msm.spec_invalid_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spec_invalid_length

/-- info: 'Challenge.Bls12381G1Msm.spec_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spec_success

end Checks.Bls12381G1MsmSpec
