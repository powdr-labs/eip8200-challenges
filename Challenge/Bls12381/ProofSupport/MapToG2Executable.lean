import Challenge.Bls12381.ProofSupport.CodecG2
import Challenge.Bls12381.ProofSupport.MapToG2Isogeny
import Challenge.Bls12381.ProofSupport.MapToG2SqrtRatioDefs
import Challenge.Bls12381.ProofSupport.ScalarMul

set_option warningAsError true

/-! # Executable shared MAP_FP2_TO_G2 operation -/

namespace Challenge.Bls12381.ProofSupport.MapToG2

/-- Source SSWU followed by the pole-aware lawful 3-isogeny. -/
def mapBeforeCofactor (u : Field) : G2Affine.Point :=
  let mapped := sourceSswu u
  iso3 mapped.xN mapped.xD mapped.y

theorem mapBeforeCofactor_eq (u : Field) :
    mapBeforeCofactor u =
      let mapped := sourceSswu u
      iso3 mapped.xN mapped.xD mapped.y := rfl

/-- First-milestone proof-friendly map: source SSWU, lawful 3-isogeny, then
naive binary multiplication by the exact RFC effective cofactor. -/
def map (u : Field) : G2Affine.Point :=
  ScalarMul.g2 hEff (mapBeforeCofactor u)

theorem map_eq (u : Field) :
    map u = ScalarMul.g2 hEff (mapBeforeCofactor u) := rfl

/-- Exact shared EIP-2537 decoded-value adapter.  The exact size check is
required because the field codec itself accepts framed windows. -/
def run (input : ByteArray) : Option ByteArray := do
  if input.size ≠ Codec.fp2Bytes then none
  let u ← Codec.decodeFp2 input 0
  pure (Codec.encodeG2 (G2Affine.toWire (map (LawfulFp2.ofWire u))))

end Challenge.Bls12381.ProofSupport.MapToG2
