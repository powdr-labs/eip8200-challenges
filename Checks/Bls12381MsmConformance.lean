import Challenge.Bls12381.Vectors
import Challenge.Bls12381.ProofSupport.CodecG1
import Challenge.Bls12381.ProofSupport.CodecG2
import Challenge.Bls12381.ProofSupport.Msm

set_option warningAsError true

/-! # Naive MSM regressions against official EIP-2537 vectors -/

namespace Checks.Bls12381MsmConformance

open Challenge.Bls12381
open Challenge.Bls12381.ProofSupport

private def scalar256Two : ScalarMul.Scalar256 :=
  ⟨2, by norm_num⟩

private def scalar256Max : ScalarMul.Scalar256 :=
  ⟨2 ^ 256 - 1, by omega⟩

private def lawfulG1Single : Bool :=
  match _hpoint : Codec.decodeG1 Vectors.g1Msm.input 0,
      hscalar : Codec.decodeScalar Vectors.g1Msm.input Codec.g1Bytes with
  | some point, some _ =>
      Codec.encodeG1 (Msm.g1Wire
        [(point, ScalarMul.scalar256OfDecode hscalar)]) ==
        Vectors.g1Msm.expected
  | _, _ => false

private def lawfulG2Single : Bool :=
  match _hpoint : Codec.decodeG2 Vectors.g2Msm.input 0,
      hscalar : Codec.decodeScalar Vectors.g2Msm.input Codec.g2Bytes with
  | some point, some _ =>
      Codec.encodeG2 (Msm.g2Wire
        [(point, ScalarMul.scalar256OfDecode hscalar)]) ==
        Vectors.g2Msm.expected
  | _, _ => false

private def lawfulG1Multi : Bool :=
  match Codec.decodeG1 Vectors.g1MsmMulti.input 0,
      Codec.decodeG1 Vectors.g1MsmMulti.input
        (Codec.g1Bytes + Codec.scalarBytes) with
  | some first, some second =>
      Codec.encodeG1 (Msm.g1Wire
        [(first, scalar256Two), (second, scalar256Two)]) ==
        Vectors.g1MsmMulti.expected
  | _, _ => false

private def lawfulG2Multi : Bool :=
  match Codec.decodeG2 Vectors.g2MsmMulti.input 0,
      Codec.decodeG2 Vectors.g2MsmMulti.input
        (Codec.g2Bytes + Codec.scalarBytes) with
  | some first, some second =>
      Codec.encodeG2 (Msm.g2Wire
        [(first, scalar256Two), (second, scalar256Two)]) ==
        Vectors.g2MsmMulti.expected
  | _, _ => false

private def lawfulG1Empty : Bool :=
  Codec.encodeG1 (Msm.g1Wire []) == Vectors.zeros Codec.g1Bytes

private def lawfulG2Empty : Bool :=
  Codec.encodeG2 (Msm.g2Wire []) == Vectors.zeros Codec.g2Bytes

private def lawfulG1ZeroAndInfinity : Bool :=
  match Codec.decodeG1 Vectors.generatorG1 0 with
  | none => false
  | some generator =>
      Codec.encodeG1 (Msm.g1Wire
        [(generator, ⟨0, by norm_num⟩), (.infinity, scalar256Max)]) ==
        Vectors.zeros Codec.g1Bytes

private def lawfulG2ZeroAndInfinity : Bool :=
  match Codec.decodeG2 Vectors.generatorG2 0 with
  | none => false
  | some generator =>
      Codec.encodeG2 (Msm.g2Wire
        [(generator, ⟨0, by norm_num⟩), (.infinity, scalar256Max)]) ==
        Vectors.zeros Codec.g2Bytes

#guard lawfulG1Single
#guard lawfulG2Single
#guard lawfulG1Multi
#guard lawfulG2Multi
#guard lawfulG1Empty
#guard lawfulG2Empty
#guard lawfulG1ZeroAndInfinity
#guard lawfulG2ZeroAndInfinity

end Checks.Bls12381MsmConformance
