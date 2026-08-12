import Challenge.Bls12381.ProofSupport.MapToG2Map
import Challenge.Bls12381.Vectors

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.MapToG2

example (u : Field) : mapBeforeCofactor u =
    let mapped := sourceSswu u
    iso3 mapped.xN mapped.xD mapped.y := mapBeforeCofactor_eq u

example (u : Field) :
    map u = ScalarMul.g2 hEff (mapBeforeCofactor u) := map_eq u

example (u : Field) : G2Affine.OnCurve (mapBeforeCofactor u) :=
  mapBeforeCofactor_onCurve u

example (u : Field) : G2Affine.OnCurve (map u) := map_onCurve u

example (u : Field) : Codec.ValidG2 (G2Affine.toWire (map u)) :=
  map_toWire_valid u

example (u : Field) :
    AffineGroup.toMathlib G2Affine.curve ⟨map u, map_onCurve u⟩ =
      hEff • AffineGroup.toMathlib G2Affine.curve
        ⟨mapBeforeCofactor u, mapBeforeCofactor_onCurve u⟩ :=
  map_nsmul u

#guard run Vectors.mapFp2ToG2.input = some Vectors.mapFp2ToG2.expected
#guard Vectors.mapFp2ToG2OfficialVectors.length = 5
#guard Vectors.mapFp2ToG2OfficialVectors.all fun vector =>
  run vector.input = some vector.expected
#guard Vectors.mapFp2ToG2FailureInputs.length = 5
#guard Vectors.mapFp2ToG2FailureInputs.all fun input => run input = none
#guard run Vectors.mapFp2ToG2FirstPaddingInvalid = none
#guard run Vectors.mapFp2ToG2SecondPaddingInvalid = none
#guard run Vectors.mapFp2ToG2SecondComponentInvalid = none

example (input output : ByteArray) :
    run input = some output ↔
      ∃ u, input.size = Codec.fp2Bytes ∧ Codec.decodeFp2 input 0 = some u ∧
        output = Codec.encodeG2 (G2Affine.toWire (map (LawfulFp2.ofWire u))) :=
  run_eq_some_iff input output

example {input : ByteArray} (hsize : input.size ≠ Codec.fp2Bytes) :
    run input = none := run_eq_none_of_wrong_length hsize

example {input : ByteArray} {i : Nat} (hsize : input.size = Codec.fp2Bytes)
    (hi : i < 16) (hnonzero : input[i]! ≠ 0) : run input = none :=
  run_eq_none_of_first_padding_nonzero hsize hi hnonzero

example {input : ByteArray} {i : Nat} (hsize : input.size = Codec.fp2Bytes)
    (hi : i < 16) (hnonzero : input[Codec.fpBytes + i]! ≠ 0) :
    run input = none :=
  run_eq_none_of_second_padding_nonzero hsize hi hnonzero

example {input : ByteArray} (hsize : input.size = Codec.fp2Bytes)
    (hvalue : EvmSemantics.Crypto.Bls12381.p ≤ Codec.fpWindowValue input 0) :
    run input = none := run_eq_none_of_first_value_ge hsize hvalue

example {input : ByteArray} (hsize : input.size = Codec.fp2Bytes)
    (hvalue : EvmSemantics.Crypto.Bls12381.p ≤
      Codec.fpWindowValue input Codec.fpBytes) :
    run input = none := run_eq_none_of_second_value_ge hsize hvalue

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.mapBeforeCofactor_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mapBeforeCofactor_eq

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.map_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_eq

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.mapBeforeCofactor_onCurve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mapBeforeCofactor_onCurve

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.map_onCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_onCurve

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.map_toWire_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_toWire_valid

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.run_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_eq_some_iff

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.run_eq_none_of_wrong_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_eq_none_of_wrong_length

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.run_eq_none_of_first_padding_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_eq_none_of_first_padding_nonzero

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.run_eq_none_of_second_padding_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_eq_none_of_second_padding_nonzero

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.run_eq_none_of_first_value_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_eq_none_of_first_value_ge

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.run_eq_none_of_second_value_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_eq_none_of_second_value_ge

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.map_nsmul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_nsmul

end Challenge.Bls12381.ProofSupport.MapToG2
