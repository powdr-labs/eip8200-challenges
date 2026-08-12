import Challenge.Bls12381MapFpToG1.Spec
import Challenge.Bls12381.ProofSupport.MapToG1Map
import Challenge.Bls12381.Vectors

set_option warningAsError true

open Challenge.Bls12381.ProofSupport

#check Challenge.Bls12381MapFpToG1.inputBytes
#check Challenge.Bls12381MapFpToG1.spec_eq_some_iff
#check Challenge.Bls12381MapFpToG1.spec_eq_none_iff

example {input output : ByteArray} :
    Challenge.Bls12381MapFpToG1.spec input = some output ↔
      ∃ u, input.size = Codec.fpBytes ∧ Codec.decodeFp input 0 = some u ∧
        output = Codec.encodeG1 (G1Affine.toWire
          (MapToG1.map (PrimeField.finEquiv u))) :=
  Challenge.Bls12381MapFpToG1.spec_eq_some_iff

example {input : ByteArray} :
    Challenge.Bls12381MapFpToG1.spec input = none ↔
      input.size ≠ Codec.fpBytes ∨ Codec.decodeFp input 0 = none :=
  Challenge.Bls12381MapFpToG1.spec_eq_none_iff

#guard Challenge.Bls12381.Vectors.mapFpToG1OfficialVectors.length = 5
#guard Challenge.Bls12381.Vectors.mapFpToG1OfficialVectors.all fun vector =>
  Challenge.Bls12381MapFpToG1.spec vector.input = some vector.expected

#guard Challenge.Bls12381.Vectors.mapFpToG1FailureInputs.length = 5
#guard Challenge.Bls12381.Vectors.mapFpToG1FailureInputs.all fun input =>
  Challenge.Bls12381MapFpToG1.spec input = none

/-- info: 'Challenge.Bls12381MapFpToG1.spec_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381MapFpToG1.spec_eq_some_iff

/-- info: 'Challenge.Bls12381MapFpToG1.spec_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381MapFpToG1.spec_eq_none_iff

/-- info: 'Challenge.Bls12381MapFpToG1.spec_invalid_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381MapFpToG1.spec_invalid_length

/-- info: 'Challenge.Bls12381MapFpToG1.spec_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381MapFpToG1.spec_success
