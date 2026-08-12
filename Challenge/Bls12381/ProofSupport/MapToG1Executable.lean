import Challenge.Bls12381.ProofSupport.CodecG1
import Challenge.Bls12381.ProofSupport.MapToG1
import Challenge.Bls12381.ProofSupport.MapToG1Isogeny
import Challenge.Bls12381.ProofSupport.MapToG1SqrtRatio
import Challenge.Bls12381.ProofSupport.ScalarMul

set_option warningAsError true

/-! # Executable shared MAP_FP_TO_G1 operation -/

namespace Challenge.Bls12381.ProofSupport.MapToG1

/-- Source SSWU followed by the pole-aware lawful 11-isogeny. -/
def mapBeforeCofactor (u : Field) : G1Affine.Point :=
  let mapped := sswuProjective sqrtRatioSource u
  iso11 mapped.xN mapped.xD mapped.y

/-- First-milestone proof-friendly map: source SSWU, lawful 11-isogeny, then
naive binary multiplication by the exact RFC effective cofactor. -/
def map (u : Field) : G1Affine.Point :=
  ScalarMul.g1 hEff (mapBeforeCofactor u)

/-- Exact shared EIP-2537 decoded-value adapter. The outer size check is
deliberate: the field codec is framed and therefore also accepts a valid
64-byte window inside a larger byte array, whereas the precompile input must
be exactly one 64-byte field element. -/
def run (input : ByteArray) : Option ByteArray := do
  if input.size ≠ Codec.fpBytes then none
  let u ← Codec.decodeFp input 0
  pure (Codec.encodeG1 (G1Affine.toWire (map (PrimeField.finEquiv u))))

end Challenge.Bls12381.ProofSupport.MapToG1
