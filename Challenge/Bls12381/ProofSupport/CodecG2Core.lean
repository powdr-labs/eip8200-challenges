import Challenge.Bls12381.ProofSupport.CodecCore
import EvmSemantics.Crypto.Bls12381.G2Add

set_option warningAsError true

/-! # Minimal G2 point-codec names and sizes -/

namespace Challenge.Bls12381.ProofSupport.Codec

open EvmSemantics.Crypto.Bls12381

abbrev decodeG2 := EvmSemantics.Crypto.Bls12381G2Add.decodePoint
abbrev encodeG2 := EvmSemantics.Crypto.Bls12381G2Add.encodePoint

def g2Bytes : Nat := 256

@[simp] theorem encodeG2_size (point : G2Point) : (encodeG2 point).size = g2Bytes := by
  unfold encodeG2
  cases point <;>
    simp [EvmSemantics.Crypto.Bls12381G2Add.encodePoint, g2Bytes, fp2Bytes]

@[simp] theorem g2Bytes_eq_semantics :
    g2Bytes = EvmSemantics.Crypto.Bls12381Codec.g2Bytes := rfl

/-- A semantic G2 point is wire-valid when it is infinity or its affine
coordinates satisfy the BLS12-381 twist equation. -/
def ValidG2 : G2Point → Prop
  | .infinity => True
  | .affine x y =>
      EvmSemantics.Crypto.G2.onCurve
        EvmSemantics.Crypto.Bls12381.g2Curve x y = true

end Challenge.Bls12381.ProofSupport.Codec
