import Challenge.Bls12381.ProofSupport.CodecScalar

set_option warningAsError true

namespace Checks.Bls12381CodecScalar

open Challenge.Bls12381.ProofSupport

example (input : ByteArray) (offset scalar : Nat) :
    Codec.decodeScalar input offset = some scalar ↔
      offset + Codec.scalarBytes ≤ input.size ∧
      Codec.scalarWindowValue input offset = scalar :=
  Codec.decodeScalar_eq_some_iff input offset scalar

example (input : ByteArray) (offset : Nat) :
    Codec.decodeScalar input offset = none ↔
      input.size < offset + Codec.scalarBytes :=
  Codec.decodeScalar_eq_none_iff input offset

example (pre suffix : ByteArray) (scalar : Nat) (hscalar : scalar < 2 ^ 256) :
    Codec.decodeScalar
      (pre ++ Codec.encodeScalar scalar hscalar ++ suffix) pre.size = some scalar :=
  Codec.decodeScalar_framed pre suffix scalar hscalar

example (input : ByteArray) (offset scalar : Nat)
    (hdecode : Codec.decodeScalar input offset = some scalar) :
    Codec.encodeScalar scalar (Codec.decodeScalar_value_lt hdecode) =
      input.extract offset (offset + Codec.scalarBytes) :=
  Codec.encodeScalar_decodeScalar hdecode

example (input : ByteArray) (offset : Nat) :
    Codec.scalarWindowValue input offset < 2 ^ 256 :=
  Codec.scalarWindowValue_lt input offset

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.encodeScalar_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeScalar_size

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeScalar_eq_some_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeScalar_eq_some_iff

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeScalar_eq_none_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeScalar_eq_none_iff

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.scalarWindowValue_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.scalarWindowValue_lt

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeScalar_value_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeScalar_value_lt

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeScalar_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeScalar_framed

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.encodeScalar_decodeScalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeScalar_decodeScalar

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.scalarWindowValue_framed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.scalarWindowValue_framed

end Checks.Bls12381CodecScalar
