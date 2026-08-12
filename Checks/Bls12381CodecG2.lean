import Challenge.Bls12381.ProofSupport.CodecG2

set_option warningAsError true

namespace Checks.Bls12381CodecG2

open EvmSemantics.Crypto.Bls12381
open Challenge.Bls12381.ProofSupport

example (input : ByteArray) (offset : Nat)
    (hx : Codec.decodeFp2 input offset = some 0)
    (hy : Codec.decodeFp2 input (offset + Codec.fp2Bytes) = some 0) :
    Codec.decodeG2 input offset = some .infinity :=
  Codec.decodeG2_eq_some_infinity hx hy

example (input : ByteArray) (offset : Nat) (x y : Fp2)
    (hx : Codec.decodeFp2 input offset = some x)
    (hy : Codec.decodeFp2 input (offset + Codec.fp2Bytes) = some y)
    (hnonzero : ¬ Codec.G2WireZero x y)
    (hcurve : EvmSemantics.Crypto.G2.onCurve
      EvmSemantics.Crypto.Bls12381.g2Curve x y = true) :
    Codec.decodeG2 input offset = some (.affine x y) :=
  Codec.decodeG2_eq_some_affine hx hy hnonzero hcurve

example (input : ByteArray) (offset : Nat) (x y : Fp2)
    (hx : Codec.decodeFp2 input offset = some x)
    (hy : Codec.decodeFp2 input (offset + Codec.fp2Bytes) = some y)
    (hnonzero : ¬ Codec.G2WireZero x y)
    (hcurve : EvmSemantics.Crypto.G2.onCurve
      EvmSemantics.Crypto.Bls12381.g2Curve x y = false) :
    Codec.decodeG2 input offset = none :=
  Codec.decodeG2_eq_none_of_offCurve hx hy hnonzero hcurve

example (input : ByteArray) (offset : Nat) (x y : Fp2)
    (hx : Codec.decodeFp2 input offset = some x)
    (hy : Codec.decodeFp2 input (offset + Codec.fp2Bytes) = some y)
    (hnonzero : ¬ Codec.G2WireZero x y) :
    Codec.decodeG2 input offset ≠ some .infinity :=
  Codec.decodeG2_nonzero_ne_infinity hx hy hnonzero

example (pre suffix : ByteArray) (point : G2Point) (hpoint : Codec.ValidG2 point) :
    Codec.decodeG2 (pre ++ Codec.encodeG2 point ++ suffix) pre.size = some point :=
  Codec.decodeG2_framed pre suffix point hpoint

example (input : ByteArray) (offset : Nat) (point : G2Point)
    (hdecode : Codec.decodeG2 input offset = some point) :
    Codec.encodeG2 point = input.extract offset (offset + Codec.g2Bytes) :=
  Codec.encodeG2_decodeG2 hdecode

example (input : ByteArray) (offset : Nat)
    (hx : Codec.decodeFp2 input offset = none) :
    Codec.decodeG2 input offset = none :=
  Codec.decodeG2_eq_none_of_first_field hx

example (input : ByteArray) (offset : Nat)
    (hy : Codec.decodeFp2 input (offset + Codec.fp2Bytes) = none) :
    Codec.decodeG2 input offset = none :=
  Codec.decodeG2_eq_none_of_second_field hy

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG2_of_components' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG2_of_components

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG2_eq_some_infinity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG2_eq_some_infinity

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG2_eq_some_affine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG2_eq_some_affine

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG2_eq_none_of_offCurve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG2_eq_none_of_offCurve

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG2_nonzero_ne_infinity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG2_nonzero_ne_infinity

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG2_eq_none_of_first_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG2_eq_none_of_first_field

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG2_eq_none_of_second_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG2_eq_none_of_second_field

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG2_success_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG2_success_cases

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG2_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG2_framed

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.encodeG2_decodeG2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeG2_decodeG2

end Checks.Bls12381CodecG2
