import Challenge.Bls12381.ProofSupport.MapToG1Map
import Challenge.Bls12381.Vectors

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.MapToG1

example (u : Field) : G1Affine.OnCurve (mapBeforeCofactor u) :=
  mapBeforeCofactor_onCurve u

example (u : Field) : G1Affine.OnCurve (map u) := map_onCurve u

example (u : Field) : Codec.ValidG1 (G1Affine.toWire (map u)) :=
  map_toWire_valid u

#guard run Vectors.mapFpToG1.input = some Vectors.mapFpToG1.expected
#guard Vectors.mapFpToG1OfficialVectors.length = 5
#guard Vectors.mapFpToG1OfficialVectors.all fun vector =>
  run vector.input = some vector.expected

example (u : Field) :
    AffineGroup.toMathlib G1Affine.curve ⟨map u, map_onCurve u⟩ =
      hEff • AffineGroup.toMathlib G1Affine.curve
        ⟨mapBeforeCofactor u, mapBeforeCofactor_onCurve u⟩ :=
  map_nsmul u

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.map_nsmul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_nsmul
#guard Vectors.mapFpToG1FailureInputs.length = 5
#guard Vectors.mapFpToG1FailureInputs.all fun input => run input = none

example (input output : ByteArray) :
    run input = some output ↔
      ∃ u, input.size = Codec.fpBytes ∧ Codec.decodeFp input 0 = some u ∧
        output = Codec.encodeG1 (G1Affine.toWire (map (PrimeField.finEquiv u))) :=
  run_eq_some_iff input output

example {input : ByteArray} (hsize : input.size ≠ Codec.fpBytes) :
    run input = none := run_eq_none_of_wrong_length hsize

example {input : ByteArray} {i : Nat} (hsize : input.size = Codec.fpBytes)
    (hi : i < 16) (hnonzero : input[i]! ≠ 0) : run input = none :=
  run_eq_none_of_padding_nonzero hsize hi hnonzero

example {input : ByteArray} (hsize : input.size = Codec.fpBytes)
    (hvalue : EvmSemantics.Crypto.Bls12381.p ≤ Codec.fpWindowValue input 0) :
    run input = none := run_eq_none_of_value_ge hsize hvalue

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.run_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_eq_some_iff

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.run_eq_none_of_wrong_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_eq_none_of_wrong_length

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.run_eq_none_of_padding_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_eq_none_of_padding_nonzero

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.run_eq_none_of_value_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_eq_none_of_value_ge

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.mapBeforeCofactor_onCurve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mapBeforeCofactor_onCurve

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.map_onCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_onCurve

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.map_toWire_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_toWire_valid

end Challenge.Bls12381.ProofSupport.MapToG1
