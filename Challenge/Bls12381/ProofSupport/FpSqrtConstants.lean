import Challenge.Bls12381.ProofSupport.FpMontgomeryPowLawful

set_option warningAsError true

/-! # Fixed exponent for source BLS12-381 base-field square roots -/

namespace Challenge.Bls12381.ProofSupport.Fp

/-- Exact 48-byte big-endian `P_PLUS_1_DIV_4` constant from `Fp.sol`. -/
def pPlus1Div4Bytes : List UInt8 := [
  0x06, 0x80, 0x44, 0x7a, 0x8e, 0x5f, 0xf9, 0xa6,
  0x92, 0xc6, 0xe9, 0xed, 0x90, 0xd2, 0xeb, 0x35,
  0xd9, 0x1d, 0xd2, 0xe1, 0x3c, 0xe1, 0x44, 0xaf,
  0xd9, 0xcc, 0x34, 0xa8, 0x3d, 0xac, 0x3d, 0x89,
  0x07, 0xaa, 0xff, 0xff, 0xac, 0x54, 0xff, 0xff,
  0xee, 0x7f, 0xbf, 0xff, 0xff, 0xff, 0xea, 0xab]

theorem length_pPlus1Div4Bytes : pPlus1Div4Bytes.length = 48 := rfl

theorem bytesValue_pPlus1Div4Bytes :
    bytesValue pPlus1Div4Bytes =
      (EvmSemantics.Crypto.Bls12381.p + 1) / 4 := by
  norm_num [pPlus1Div4Bytes, bytesValue, UInt8.toNat_ofNat,
    EvmSemantics.Crypto.Bls12381.p, EvmSemantics.Crypto.Bls12381.absU]

end Challenge.Bls12381.ProofSupport.Fp
