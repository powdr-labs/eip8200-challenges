import Challenge.Bls12381.ProofSupport.CodecRepresentation

set_option warningAsError true

namespace Checks.Bls12381CodecRepresentation

open Challenge.Bls12381.ProofSupport

example (a : Fp.Limbs) : (Codec.encodeFpLimbs48 a).size = 48 :=
  Codec.encodeFpLimbs48_size a

example (a : Fp.Limbs) (ha : Fp.Canonical a) :
    Codec.encodeFp (Fp.toField a) =
      ByteArray.mk (Array.replicate 16 0) ++ Codec.encodeFpLimbs48 a :=
  Codec.encodeFp_toField_eq_padded_limbs ha

example (pre suffix : ByteArray) (a : Fp.Limbs) (ha : Fp.Canonical a) :
    Codec.decodeFp
      (pre ++ ByteArray.mk (Array.replicate 16 0) ++
        Codec.encodeFpLimbs48 a ++ suffix) pre.size = some (Fp.toField a) :=
  Codec.decodeFp_framed_limbs pre suffix ha

example (a b : Fp.Limbs) (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Codec.encodeFpLimbs48 a = Codec.encodeFpLimbs48 b ↔
      Fp.value a = Fp.value b :=
  Codec.encodeFpLimbs48_eq_iff ha hb

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.encodeFpLimbs48_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeFpLimbs48_size

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.bytesToBigEndianNat_encodeFpLimbs48' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.bytesToBigEndianNat_encodeFpLimbs48

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.encodeFp_toField_eq_padded_limbs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeFp_toField_eq_padded_limbs

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeFp_framed_limbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeFp_framed_limbs

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.encodeFpLimbs48_injective_of_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeFpLimbs48_injective_of_canonical

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.encodeFpLimbs48_eq_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeFpLimbs48_eq_iff

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.encodeFp_toField_eq_iff_limbs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeFp_toField_eq_iff_limbs

end Checks.Bls12381CodecRepresentation
