import Challenge.Bls12381.Vectors
import Challenge.Bls12381.ProofSupport.CodecG1
import Challenge.Bls12381.ProofSupport.CodecG2
import Challenge.Bls12381.ProofSupport.ScalarMul

set_option warningAsError true

/-! # Naive scalar multiplication regressions against EIP-2537 vectors -/

namespace Checks.Bls12381ScalarMulConformance

open Challenge.Bls12381
open Challenge.Bls12381.ProofSupport

private def lawfulG1ScalarVector : Bool :=
  match _hpoint : Codec.decodeG1 Vectors.g1Msm.input 0,
      hscalar : Codec.decodeScalar Vectors.g1Msm.input Codec.g1Bytes with
  | some point, some _ =>
      let scalar := ScalarMul.scalar256OfDecode hscalar
      Codec.encodeG1 (G1Affine.toWire
        (ScalarMul.g1Eip scalar (G1Affine.ofWire point))) ==
        Vectors.g1Msm.expected
  | _, _ => false

private def lawfulG2ScalarVector : Bool :=
  match _hpoint : Codec.decodeG2 Vectors.g2Msm.input 0,
      hscalar : Codec.decodeScalar Vectors.g2Msm.input Codec.g2Bytes with
  | some point, some _ =>
      let scalar := ScalarMul.scalar256OfDecode hscalar
      Codec.encodeG2 (G2Affine.toWire
        (ScalarMul.g2Eip scalar (G2Affine.ofWire point))) ==
        Vectors.g2Msm.expected
  | _, _ => false

private def lawfulG1ZeroScalar : Bool :=
  match Codec.decodeG1 Vectors.generatorG1 0 with
  | none => false
  | some point => Codec.encodeG1 (ScalarMul.g1Wire 0 point) ==
      Vectors.zeros Codec.g1Bytes

private def lawfulG2ZeroScalar : Bool :=
  match Codec.decodeG2 Vectors.generatorG2 0 with
  | none => false
  | some point => Codec.encodeG2 (ScalarMul.g2Wire 0 point) ==
      Vectors.zeros Codec.g2Bytes

private def lawfulG1InfinityMaxScalar : Bool :=
  Codec.encodeG1 (ScalarMul.g1Wire (2 ^ 256 - 1) .infinity) ==
    Vectors.zeros Codec.g1Bytes

private def lawfulG2InfinityMaxScalar : Bool :=
  Codec.encodeG2 (ScalarMul.g2Wire (2 ^ 256 - 1) .infinity) ==
    Vectors.zeros Codec.g2Bytes

#guard lawfulG1ScalarVector
#guard lawfulG2ScalarVector
#guard lawfulG1ZeroScalar
#guard lawfulG2ZeroScalar
#guard lawfulG1InfinityMaxScalar
#guard lawfulG2InfinityMaxScalar

end Checks.Bls12381ScalarMulConformance
