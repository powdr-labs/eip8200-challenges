import EvmSemantics.EVM.BigStep
import Challenge.Bls12381G1Add.Constants
import Challenge.Bls12381.ProofSupport.CodecG1
import Challenge.Bls12381.ProofSupport.G1Affine

set_option warningAsError true

namespace Challenge.Bls12381G1Add

open EvmSemantics EvmSemantics.EVM

/--
EIP-correct G1ADD adapter at the decoded affine boundary.  Unlike the pinned
`Crypto.Bls12381G1Add.run?`, addition is routed through the local lawful-field
semantics and therefore does not depend on the opaque pinned `Fin` inverse.
Ordinary G1 decoding deliberately performs no prime-subgroup check.
-/
def spec (input : ByteArray) : Option ByteArray :=
  if input.size ≠ inputBytes then none
  else do
    let left ← Challenge.Bls12381.ProofSupport.Codec.decodeG1 input 0
    let right ← Challenge.Bls12381.ProofSupport.Codec.decodeG1 input
      Challenge.Bls12381.ProofSupport.Codec.g1Bytes
    some (Challenge.Bls12381.ProofSupport.Codec.encodeG1
      (Challenge.Bls12381.ProofSupport.G1Affine.toWire
        (Challenge.Bls12381.ProofSupport.G1Affine.add
          (Challenge.Bls12381.ProofSupport.G1Affine.ofWire left)
          (Challenge.Bls12381.ProofSupport.G1Affine.ofWire right))))

theorem spec_eq_some_iff {input output : ByteArray} :
    spec input = some output ↔
      input.size = inputBytes ∧
      ∃ left right,
        Challenge.Bls12381.ProofSupport.Codec.decodeG1 input 0 = some left ∧
        Challenge.Bls12381.ProofSupport.Codec.decodeG1 input
          Challenge.Bls12381.ProofSupport.Codec.g1Bytes = some right ∧
        output = Challenge.Bls12381.ProofSupport.Codec.encodeG1
          (Challenge.Bls12381.ProofSupport.G1Affine.toWire
            (Challenge.Bls12381.ProofSupport.G1Affine.add
              (Challenge.Bls12381.ProofSupport.G1Affine.ofWire left)
              (Challenge.Bls12381.ProofSupport.G1Affine.ofWire right))) := by
  unfold spec
  by_cases hsize : input.size = inputBytes
  · rw [if_neg (not_not_intro hsize)]
    cases hleft : Challenge.Bls12381.ProofSupport.Codec.decodeG1 input 0 with
    | none => simp_all
    | some left =>
        cases hright : Challenge.Bls12381.ProofSupport.Codec.decodeG1 input
            Challenge.Bls12381.ProofSupport.Codec.g1Bytes with
        | none => simp_all
        | some right => simp_all [eq_comm]
  · rw [if_pos hsize]
    simp [hsize]

theorem spec_eq_none_iff {input : ByteArray} :
    spec input = none ↔
      input.size ≠ inputBytes ∨
      Challenge.Bls12381.ProofSupport.Codec.decodeG1 input 0 = none ∨
      Challenge.Bls12381.ProofSupport.Codec.decodeG1 input
        Challenge.Bls12381.ProofSupport.Codec.g1Bytes = none := by
  unfold spec
  by_cases hsize : input.size = inputBytes
  · rw [if_neg (not_not_intro hsize)]
    cases hleft : Challenge.Bls12381.ProofSupport.Codec.decodeG1 input 0 with
    | none => simp_all
    | some left =>
        cases hright : Challenge.Bls12381.ProofSupport.Codec.decodeG1 input
            Challenge.Bls12381.ProofSupport.Codec.g1Bytes with
        | none => simp_all
        | some right => simp_all
  · rw [if_pos hsize]
    simp [hsize]

theorem spec_invalid_length {input : ByteArray}
    (hsize : input.size ≠ inputBytes) : spec input = none := by
  exact spec_eq_none_iff.mpr (Or.inl hsize)

theorem spec_success {input : ByteArray} {left right : Crypto.Bls12381.Point}
    (hsize : input.size = inputBytes)
    (hleft : Challenge.Bls12381.ProofSupport.Codec.decodeG1 input 0 = some left)
    (hright : Challenge.Bls12381.ProofSupport.Codec.decodeG1 input
      Challenge.Bls12381.ProofSupport.Codec.g1Bytes = some right) :
    spec input = some (Challenge.Bls12381.ProofSupport.Codec.encodeG1
      (Challenge.Bls12381.ProofSupport.G1Affine.toWire
        (Challenge.Bls12381.ProofSupport.G1Affine.add
          (Challenge.Bls12381.ProofSupport.G1Affine.ofWire left)
          (Challenge.Bls12381.ProofSupport.G1Affine.ofWire right)))) := by
  apply spec_eq_some_iff.mpr
  exact ⟨hsize, left, right, hleft, hright, rfl⟩

/-- Source calldata must fit the 256-bit `calldatasize` word. -/
def CalldataFits (input : ByteArray) : Prop := input.size < 2 ^ 256

end Challenge.Bls12381G1Add
