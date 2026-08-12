import Challenge.Bls12381.Vectors
import Challenge.Bls12381G2Msm.SpecRefinement

set_option warningAsError true

namespace Checks.Bls12381G2MsmSpec

open Challenge.Bls12381
open Challenge.Bls12381.ProofSupport
open Challenge.Bls12381G2Msm

private def oneByte : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded 1 1

private def paddingInvalid : ByteArray :=
  oneByte ++ Vectors.zeros 287

private def fieldInvalid : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded
      EvmSemantics.Crypto.Bls12381.p 64 ++
    Vectors.zeros 224

private def offCurve : ByteArray :=
  Vectors.zeros 192 ++
    EvmSemantics.Data.Bytes.natToBytesPadded 1 64 ++
    Vectors.zeros 32

private def maxScalarInput : ByteArray :=
  Vectors.generatorG2 ++
    EvmSemantics.Data.Bytes.natToBytesPadded (2 ^ 256 - 1) 32

private def decodesMaxScalar : Bool :=
  match decodeTerm maxScalarInput 0 with
  | some (_, scalar) => scalar.val == 2 ^ 256 - 1
  | none => false

example (input : ByteArray) (offset : Nat) :
    ScalarMul.Scalar256 := scalarAt input offset

example (input : ByteArray) (offset : Nat) :
    Option Msm.G2WireTerm := decodeTerm input offset

example (input : ByteArray) (offset count : Nat) :
    Option (List Msm.G2WireTerm) := decodeTerms input offset count

example (input : ByteArray) (offset : Nat) (term : Msm.G2WireTerm) :
    decodeTerm input offset = some term ↔
      Codec.decodeG2Subgroup input offset = some term.1 ∧
      Codec.decodeScalar input (offset + Codec.g2Bytes) = some term.2.val :=
  decodeTerm_eq_some_iff input offset term

example {input : ByteArray} {offset count : Nat}
    {terms : List Msm.G2WireTerm}
    (hdecode : decodeTerms input offset count = some terms) :
    terms.length = count := decodeTerms_length hdecode

example {input : ByteArray} {offset : Nat} {term : Msm.G2WireTerm}
    (hdecode : decodeTerm input offset = some term) :
    Subgroup.g2 term.1 = true := decodeTerm_subgroup hdecode

example {input output : ByteArray} : spec input = some output ↔
    input.size ≠ 0 ∧ input.size % pairBytes = 0 ∧
      ∃ terms, decodeTerms input 0 (input.size / pairBytes) = some terms ∧
        output = Codec.encodeG2 (Msm.g2Wire terms) :=
  spec_eq_some_iff

example {input : ByteArray} : spec input = none ↔
    input.size = 0 ∨ input.size % pairBytes ≠ 0 ∨
      decodeTerms input 0 (input.size / pairBytes) = none :=
  spec_eq_none_iff

#guard pairBytes = Codec.g2Bytes + Codec.scalarBytes
#guard spec ByteArray.empty = none
#guard spec (Vectors.zeros 287) = none
#guard spec (Vectors.zeros 289) = none
#guard spec (Vectors.zeros 288) = some (Vectors.zeros Codec.g2Bytes)
#guard spec (Vectors.zeros 576) = some (Vectors.zeros Codec.g2Bytes)
#guard spec paddingInvalid = none
#guard spec fieldInvalid = none
#guard spec offCurve = none
#guard spec Vectors.g2MsmNonSubgroup = none
#guard spec Vectors.g2Msm.input = some Vectors.g2Msm.expected
#guard spec Vectors.g2MsmMulti.input = some Vectors.g2MsmMulti.expected
#guard decodesMaxScalar

/-! The adapter theorems use only Lean's standard quotient and propositional
extensionality axioms plus classical choice. -/

/-- info: 'Challenge.Bls12381G2Msm.decodeTerm_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decodeTerm_eq_some_iff

/-- info: 'Challenge.Bls12381G2Msm.decodeTerm_subgroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decodeTerm_subgroup

/-- info: 'Challenge.Bls12381G2Msm.decodeTerms_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decodeTerms_length

/-- info: 'Challenge.Bls12381G2Msm.spec_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spec_eq_some_iff

/-- info: 'Challenge.Bls12381G2Msm.spec_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spec_eq_none_iff

/-- info: 'Challenge.Bls12381G2Msm.spec_invalid_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spec_invalid_length

/-- info: 'Challenge.Bls12381G2Msm.spec_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spec_success

end Checks.Bls12381G2MsmSpec
