import Challenge.Bls12381.ProofSupport.CodecG1

set_option warningAsError true

namespace Checks.Bls12381CodecG1

open EvmSemantics.Crypto.Bls12381
open Challenge.Bls12381.ProofSupport

example (input : ByteArray) (offset : Nat)
    (hx : Codec.decodeFp input offset = some 0)
    (hy : Codec.decodeFp input (offset + Codec.fpBytes) = some 0) :
    Codec.decodeG1 input offset = some .infinity :=
  Codec.decodeG1_eq_some_infinity hx hy

example (input : ByteArray) (offset : Nat) (x y : Fp)
    (hx : Codec.decodeFp input offset = some x)
    (hy : Codec.decodeFp input (offset + Codec.fpBytes) = some y)
    (hnonzero : ¬(x.val = 0 ∧ y.val = 0))
    (hcurve : EvmSemantics.Crypto.Bls12381.onCurve x y = true) :
    Codec.decodeG1 input offset = some (.affine x y) :=
  Codec.decodeG1_eq_some_affine hx hy hnonzero hcurve

example (input : ByteArray) (offset : Nat) (x y : Fp)
    (hx : Codec.decodeFp input offset = some x)
    (hy : Codec.decodeFp input (offset + Codec.fpBytes) = some y)
    (hnonzero : ¬(x.val = 0 ∧ y.val = 0))
    (hcurve : EvmSemantics.Crypto.Bls12381.onCurve x y = false) :
    Codec.decodeG1 input offset = none :=
  Codec.decodeG1_eq_none_of_offCurve hx hy hnonzero hcurve

example (input : ByteArray) (offset : Nat) (x y : Fp)
    (hx : Codec.decodeFp input offset = some x)
    (hy : Codec.decodeFp input (offset + Codec.fpBytes) = some y)
    (hnonzero : ¬(x.val = 0 ∧ y.val = 0)) :
    Codec.decodeG1 input offset ≠ some .infinity :=
  Codec.decodeG1_nonzero_ne_infinity hx hy hnonzero

example (pre suffix : ByteArray) (point : Point) (hpoint : Codec.ValidG1 point) :
    Codec.decodeG1 (pre ++ Codec.encodeG1 point ++ suffix) pre.size = some point :=
  Codec.decodeG1_framed pre suffix point hpoint

example (input : ByteArray) (offset : Nat) (point : Point)
    (hdecode : Codec.decodeG1 input offset = some point) :
    Codec.encodeG1 point = input.extract offset (offset + Codec.g1Bytes) :=
  Codec.encodeG1_decodeG1 hdecode

example (input : ByteArray) (offset : Nat)
    (hx : Codec.decodeFp input offset = none) :
    Codec.decodeG1 input offset = none :=
  Codec.decodeG1_eq_none_of_first_field hx

example (input : ByteArray) (offset : Nat)
    (hy : Codec.decodeFp input (offset + Codec.fpBytes) = none) :
    Codec.decodeG1 input offset = none :=
  Codec.decodeG1_eq_none_of_second_field hy

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG1_of_components' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG1_of_components

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG1_eq_some_infinity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG1_eq_some_infinity

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG1_eq_some_affine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG1_eq_some_affine

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG1_eq_none_of_offCurve' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG1_eq_none_of_offCurve

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG1_nonzero_ne_infinity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG1_nonzero_ne_infinity

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG1_eq_none_of_first_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG1_eq_none_of_first_field

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG1_eq_none_of_second_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG1_eq_none_of_second_field

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG1_success_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG1_success_cases

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG1_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG1_framed

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.encodeG1_decodeG1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeG1_decodeG1

end Checks.Bls12381CodecG1
