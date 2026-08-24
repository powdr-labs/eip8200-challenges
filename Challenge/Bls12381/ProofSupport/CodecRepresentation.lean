import Challenge.Bls12381.ProofSupport.CodecFp
import Challenge.Bls12381.ProofSupport.FpRepresentation

set_option warningAsError true

/-! # Canonical source limbs and EIP-2537 field encoding -/

namespace Challenge.Bls12381.ProofSupport.Codec

open EvmSemantics.Crypto.Bls12381

/-- The source-side 48-byte canonical encoding of a decoded limb pair. -/
def encodeFpLimbs48 (a : Fp.Limbs) : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded (Fp.value a) 48

@[simp] theorem encodeFpLimbs48_size (a : Fp.Limbs) :
    (encodeFpLimbs48 a).size = 48 := by
  simp [encodeFpLimbs48,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]

theorem bytesToBigEndianNat_encodeFpLimbs48 {a : Fp.Limbs}
    (ha : Fp.Canonical a) :
    EvmSemantics.Data.Bytes.bytesToBigEndianNat (encodeFpLimbs48 a) =
      Fp.value a := by
  apply Challenge.EvmProof.Memory.bytesToBigEndianNat_natToBytesPadded
  exact ha.2.trans (by norm_num [p, absU])

theorem encodeFp_toField_eq_padded_limbs {a : Fp.Limbs}
    (ha : Fp.Canonical a) :
    encodeFp (Fp.toField a) =
      ByteArray.mk (Array.replicate 16 0) ++ encodeFpLimbs48 a := by
  unfold encodeFp EvmSemantics.Crypto.Bls12381Codec.encodeFp
  have hval : (Fp.toField a).val = Fp.value a := by
    simp [Fp.toField, Nat.mod_eq_of_lt ha.2]
  rw [hval]
  change EvmSemantics.Data.Bytes.natToBytesPadded (Fp.value a) 64 = _
  rw [show 64 = 16 + 48 by omega,
    Challenge.EvmProof.ByteWindow.natToBytesPadded_prefix_zeros
      (Fp.value a) 16 48 (ha.2.trans (by norm_num [p, absU]))]
  rfl

theorem decodeFp_framed_limbs (pre suffix : ByteArray) {a : Fp.Limbs}
    (ha : Fp.Canonical a) :
    decodeFp
      (pre ++ ByteArray.mk (Array.replicate 16 0) ++
        encodeFpLimbs48 a ++ suffix) pre.size = some (Fp.toField a) := by
  have h := decodeFp_framed pre suffix (Fp.toField a)
  rw [encodeFp_toField_eq_padded_limbs ha] at h
  simpa [ByteArray.append_assoc] using h

theorem encodeFpLimbs48_injective_of_canonical {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b)
    (hencode : encodeFpLimbs48 a = encodeFpLimbs48 b) :
    Fp.value a = Fp.value b := by
  rw [← bytesToBigEndianNat_encodeFpLimbs48 ha,
    ← bytesToBigEndianNat_encodeFpLimbs48 hb]
  exact congrArg EvmSemantics.Data.Bytes.bytesToBigEndianNat hencode

theorem encodeFpLimbs48_eq_iff {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    encodeFpLimbs48 a = encodeFpLimbs48 b ↔ Fp.value a = Fp.value b := by
  constructor
  · exact encodeFpLimbs48_injective_of_canonical ha hb
  · intro hvalue
    simp [encodeFpLimbs48, hvalue]

theorem encodeFp_toField_eq_iff_limbs {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    encodeFp (Fp.toField a) = encodeFp (Fp.toField b) ↔
      encodeFpLimbs48 a = encodeFpLimbs48 b := by
  rw [encodeFp_toField_eq_padded_limbs ha,
    encodeFp_toField_eq_padded_limbs hb]
  exact ByteArray.append_right_inj _

end Challenge.Bls12381.ProofSupport.Codec
