import Challenge.Bls12381.ProofSupport.Codec

set_option warningAsError true

namespace Checks.Bls12381Codec

open EvmSemantics.Crypto.Bls12381
open Challenge.Bls12381.ProofSupport

example (a : Fp) : (Codec.encodeFp a).size = Codec.fpBytes :=
  Codec.encodeFp_size a

example (a : Fp2) : (Codec.encodeFp2 a).size = Codec.fp2Bytes :=
  Codec.encodeFp2_size a

example (a : Fp2) : Codec.decodeFp2 (Codec.encodeFp2 a) 0 = some a :=
  Codec.decodeFp2_encodeFp2 a

example (point : Point) : (Codec.encodeG1 point).size = Codec.g1Bytes :=
  Codec.encodeG1_size point

example (point : G2Point) : (Codec.encodeG2 point).size = Codec.g2Bytes :=
  Codec.encodeG2_size point

example (point : Point) (hpoint : Codec.ValidG1 point) :
    Codec.decodeG1 (Codec.encodeG1 point) 0 = some point :=
  Codec.decodeG1_encodeG1 point hpoint

example (point : G2Point) (hpoint : Codec.ValidG2 point) :
    Codec.decodeG2 (Codec.encodeG2 point) 0 = some point :=
  Codec.decodeG2_encodeG2 point hpoint

example (input : ByteArray) (offset : Nat)
    (hshort : input.size < offset + Codec.fpBytes) :
    Codec.decodeFp input offset = none :=
  Codec.decodeFp_eq_none_of_short hshort

example (input : ByteArray) (offset : Nat)
    (hsize : offset + Codec.fpBytes ≤ input.size)
    (hnonzero : input[offset]! ≠ 0) :
    Codec.decodeFp input offset = none :=
  Codec.decodeFp_eq_none_of_first_padding_nonzero hsize hnonzero

example (input : ByteArray) (offset : Nat)
    (hshort : input.size < offset + Codec.fp2Bytes) :
    Codec.decodeFp2 input offset = none :=
  Codec.decodeFp2_eq_none_of_short hshort

example (input : ByteArray) (offset : Nat)
    (hshort : input.size < offset + Codec.g1Bytes) :
    Codec.decodeG1 input offset = none :=
  Codec.decodeG1_eq_none_of_short hshort

example (input : ByteArray) (offset : Nat)
    (hshort : input.size < offset + Codec.g2Bytes) :
    Codec.decodeG2 input offset = none :=
  Codec.decodeG2_eq_none_of_short hshort

#print axioms Codec.decodeFp2_encodeFp2
#print axioms Codec.decodeG1_encodeG1
#print axioms Codec.decodeG2_encodeG2
#print axioms Codec.decodeFp_eq_none_of_first_padding_nonzero
#print axioms Codec.decodeG1_eq_none_of_short
#print axioms Codec.decodeG2_eq_none_of_short

end Checks.Bls12381Codec
