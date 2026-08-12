import Challenge.Bls12381.ProofSupport.CodecFp2

set_option warningAsError true

namespace Checks.Bls12381CodecFp2

open EvmSemantics.Crypto.Bls12381
open Challenge.Bls12381.ProofSupport

example (input : ByteArray) (offset : Nat) (a : Fp2) :
    Codec.decodeFp2 input offset = some a ↔
      offset + Codec.fp2Bytes ≤ input.size ∧
      Codec.PaddingZero input offset ∧
      Codec.fpWindowValue input offset = a.c0.val ∧
      Codec.PaddingZero input (offset + Codec.fpBytes) ∧
      Codec.fpWindowValue input (offset + Codec.fpBytes) = a.c1.val :=
  Codec.decodeFp2_eq_some_iff input offset a

example (pre suffix : ByteArray) (a : Fp2) :
    Codec.decodeFp2 (pre ++ Codec.encodeFp2 a ++ suffix) pre.size = some a :=
  Codec.decodeFp2_framed pre suffix a

example (input : ByteArray) (offset : Nat) (a : Fp2)
    (hdecode : Codec.decodeFp2 input offset = some a) :
    Codec.encodeFp2 a = input.extract offset (offset + Codec.fp2Bytes) :=
  Codec.encodeFp2_decodeFp2 hdecode

example (input : ByteArray) (offset i : Nat)
    (hsize : offset + Codec.fp2Bytes ≤ input.size) (hi : i < 16)
    (hnonzero : input[offset + i]! ≠ 0) :
    Codec.decodeFp2 input offset = none :=
  Codec.decodeFp2_eq_none_of_first_padding_nonzero hsize hi hnonzero

example (input : ByteArray) (offset i : Nat)
    (hsize : offset + Codec.fp2Bytes ≤ input.size) (hi : i < 16)
    (hnonzero : input[offset + Codec.fpBytes + i]! ≠ 0) :
    Codec.decodeFp2 input offset = none :=
  Codec.decodeFp2_eq_none_of_second_padding_nonzero hsize hi hnonzero

example (input : ByteArray) (offset : Nat)
    (hsize : offset + Codec.fp2Bytes ≤ input.size)
    (hvalue : p ≤ Codec.fpWindowValue input offset) :
    Codec.decodeFp2 input offset = none :=
  Codec.decodeFp2_eq_none_of_first_value_ge hsize hvalue

example (input : ByteArray) (offset : Nat)
    (hsize : offset + Codec.fp2Bytes ≤ input.size)
    (hvalue : p ≤ Codec.fpWindowValue input (offset + Codec.fpBytes)) :
    Codec.decodeFp2 input offset = none :=
  Codec.decodeFp2_eq_none_of_second_value_ge hsize hvalue

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeFp2_eq_some_iff_components' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFp2_eq_some_iff_components

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeFp2_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFp2_eq_some_iff

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeFp2_eq_none_of_first_padding_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFp2_eq_none_of_first_padding_nonzero

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeFp2_eq_none_of_second_padding_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFp2_eq_none_of_second_padding_nonzero

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeFp2_eq_none_of_first_value_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFp2_eq_none_of_first_value_ge

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeFp2_eq_none_of_second_value_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFp2_eq_none_of_second_value_ge

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeFp2_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFp2_framed

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.encodeFp2_decodeFp2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeFp2_decodeFp2

end Checks.Bls12381CodecFp2
