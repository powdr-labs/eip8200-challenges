import Challenge.Bls12381.ProofSupport.Fp

set_option warningAsError true

/-! # Shared BLS12-381 base-field word constants -/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics
open EvmSemantics.Crypto.Bls12381

def modulusLo : UInt256 := UInt256.ofNat
  0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

def modulusHi : UInt256 := UInt256.ofNat
  0x1a0111ea397fe69a4b1ba7b6434bacd7

theorem modulus_words :
    modulusLo.toNat + Challenge.EvmProof.Limbs.radix * modulusHi.toNat = p := by
  norm_num [modulusLo, modulusHi, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Limbs.radix, p, absU]

end Challenge.Bls12381.ProofSupport.Fp
