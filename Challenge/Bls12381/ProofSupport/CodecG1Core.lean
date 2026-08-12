import Challenge.Bls12381.ProofSupport.CodecCore
import EvmSemantics.Crypto.Bls12381.G1Add

set_option warningAsError true

/-! # Minimal G1 point-codec names and sizes -/

namespace Challenge.Bls12381.ProofSupport.Codec

open EvmSemantics.Crypto.Bls12381

abbrev decodeG1 := EvmSemantics.Crypto.Bls12381G1Add.decodePoint
abbrev encodeG1 := EvmSemantics.Crypto.Bls12381G1Add.encodePoint

def g1Bytes : Nat := 128

@[simp] theorem encodeG1_size (point : Point) : (encodeG1 point).size = g1Bytes := by
  unfold encodeG1
  cases point <;>
    simp [EvmSemantics.Crypto.Bls12381G1Add.encodePoint, g1Bytes, fpBytes]

@[simp] theorem g1Bytes_eq_semantics :
    g1Bytes = EvmSemantics.Crypto.Bls12381Codec.g1Bytes := rfl

/-- A semantic G1 point is wire-valid when it is infinity or its affine
coordinates satisfy the BLS12-381 curve equation. -/
def ValidG1 : Point → Prop
  | .infinity => True
  | .affine x y => EvmSemantics.Crypto.Bls12381.onCurve x y = true

end Challenge.Bls12381.ProofSupport.Codec
