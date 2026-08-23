import EvmSemantics.Crypto.Bls12381.Codec
import YulEvmCompiler.BytesLemmas

set_option warningAsError true

/-! # Minimal shared BLS field-codec names and sizes -/

namespace Challenge.Bls12381.ProofSupport.Codec

open EvmSemantics.Crypto.Bls12381

abbrev decodeFp := EvmSemantics.Crypto.Bls12381Codec.decodeFp
abbrev decodeFp2 := EvmSemantics.Crypto.Bls12381Codec.decodeFp2
abbrev encodeFp := EvmSemantics.Crypto.Bls12381Codec.encodeFp
abbrev encodeFp2 := EvmSemantics.Crypto.Bls12381Codec.encodeFp2

def fpBytes : Nat := 64
def fp2Bytes : Nat := 128

@[simp] theorem encodeFp_size (a : Fp) : (encodeFp a).size = fpBytes := by
  exact YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ _

@[simp] theorem encodeFp2_size (a : Fp2) : (encodeFp2 a).size = fp2Bytes := by
  unfold encodeFp2 EvmSemantics.Crypto.Bls12381Codec.encodeFp2
  simp [fp2Bytes, fpBytes]

@[simp] theorem fpBytes_eq_semantics :
    fpBytes = EvmSemantics.Crypto.Bls12381Codec.fpBytes := rfl

@[simp] theorem fp2Bytes_eq_semantics :
    fp2Bytes = EvmSemantics.Crypto.Bls12381Codec.fp2Bytes := rfl

end Challenge.Bls12381.ProofSupport.Codec
