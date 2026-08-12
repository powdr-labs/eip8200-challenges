import Challenge.Bls12381.ProofSupport.Fp2Representation
import Challenge.Bls12381.ProofSupport.FpSqrtConstants

set_option warningAsError true

/-! # Fixed source constants for BLS12-381 Fp2 square roots -/

namespace Challenge.Bls12381.ProofSupport.Fp2

open EvmSemantics

/-- Exact 48-byte big-endian `INV_TWO` constant from `Fp2.sol`. -/
def invTwoBytes : List UInt8 := [
  0x0d, 0x00, 0x88, 0xf5, 0x1c, 0xbf, 0xf3, 0x4d,
  0x25, 0x8d, 0xd3, 0xdb, 0x21, 0xa5, 0xd6, 0x6b,
  0xb2, 0x3b, 0xa5, 0xc2, 0x79, 0xc2, 0x89, 0x5f,
  0xb3, 0x98, 0x69, 0x50, 0x7b, 0x58, 0x7b, 0x12,
  0x0f, 0x55, 0xff, 0xff, 0x58, 0xa9, 0xff, 0xff,
  0xdc, 0xff, 0x7f, 0xff, 0xff, 0xff, 0xd5, 0x56]

theorem length_invTwoBytes : invTwoBytes.length = 48 := rfl

theorem bytesValue_invTwoBytes :
    Fp.bytesValue invTwoBytes =
      (EvmSemantics.Crypto.Bls12381.p + 1) / 2 := by
  norm_num [invTwoBytes, Fp.bytesValue, UInt8.toNat_ofNat,
    EvmSemantics.Crypto.Bls12381.p, EvmSemantics.Crypto.Bls12381.absU]

/-- Canonical decoded limb representation of the source constant. -/
def invTwo : Fp.Limbs :=
  { hi := UInt256.ofNat 0x0d0088f51cbff34d258dd3db21a5d66b
    lo := UInt256.ofNat
      0xb23ba5c279c2895fb39869507b587b120f55ffff58a9ffffdcff7fffffffd556 }

@[simp] theorem value_invTwo : Fp.value invTwo =
    (EvmSemantics.Crypto.Bls12381.p + 1) / 2 := by
  norm_num [invTwo, Fp.value, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Limbs.radix, EvmSemantics.Crypto.Bls12381.p,
    EvmSemantics.Crypto.Bls12381.absU]

theorem canonical_invTwo : Fp.Canonical invTwo := by
  apply Fp.canonical_of_value_lt
  rw [value_invTwo]
  norm_num [EvmSemantics.Crypto.Bls12381.p,
    EvmSemantics.Crypto.Bls12381.absU]

end Challenge.Bls12381.ProofSupport.Fp2
