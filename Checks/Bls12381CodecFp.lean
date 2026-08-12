import Challenge.Bls12381.ProofSupport.CodecFp

set_option warningAsError true

namespace Checks.Bls12381CodecFp

open EvmSemantics.Crypto.Bls12381
open Challenge.Bls12381.ProofSupport

example (input : ByteArray) (offset : Nat) :
    (Codec.decodeFp input offset).isSome = true ↔
      offset + Codec.fpBytes ≤ input.size ∧
      Codec.PaddingZero input offset ∧
      Codec.fpWindowValue input offset < p :=
  Codec.decodeFp_isSome_iff input offset

example (input : ByteArray) (offset : Nat) (a : Fp) :
    Codec.decodeFp input offset = some a ↔
      offset + Codec.fpBytes ≤ input.size ∧
      Codec.PaddingZero input offset ∧
      Codec.fpWindowValue input offset = a.val :=
  Codec.decodeFp_eq_some_iff input offset a

example (input : ByteArray) (offset i : Nat)
    (hsize : offset + Codec.fpBytes ≤ input.size) (hi : i < 16)
    (hnonzero : input[offset + i]! ≠ 0) :
    Codec.decodeFp input offset = none :=
  Codec.decodeFp_eq_none_of_padding_nonzero hsize hi hnonzero

example (input : ByteArray) (offset : Nat)
    (hsize : offset + Codec.fpBytes ≤ input.size)
    (hvalue : p ≤ Codec.fpWindowValue input offset) :
    Codec.decodeFp input offset = none :=
  Codec.decodeFp_eq_none_of_value_ge hsize hvalue

example (input : ByteArray) (offset : Nat) (a : Fp)
    (hdecode : Codec.decodeFp input offset = some a) :
    Codec.encodeFp a =
      input.extract offset (offset + Codec.fpBytes) :=
  Codec.encodeFp_decodeFp hdecode

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.paddingZero_iff_forall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.paddingZero_iff_forall

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeFp_eq_none_of_padding_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFp_eq_none_of_padding_nonzero

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeFp_eq_none_of_value_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFp_eq_none_of_value_ge

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeFp_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFp_eq_some_iff

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeFp_isSome_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFp_isSome_iff

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.encodeFp_decodeFp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeFp_decodeFp

end Checks.Bls12381CodecFp
