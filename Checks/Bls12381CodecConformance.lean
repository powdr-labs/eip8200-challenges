import Challenge.Bls12381.Vectors
import Challenge.Bls12381.ProofSupport.CodecFp
import Challenge.Bls12381.ProofSupport.CodecFp2
import Challenge.Bls12381.ProofSupport.CodecG1
import Challenge.Bls12381.ProofSupport.CodecG2
import Challenge.Bls12381.ProofSupport.CodecScalar
import Challenge.Bls12381.ProofSupport.CodecSubgroup

set_option warningAsError true

/-! # Official-vector codec regressions -/

namespace Checks.Bls12381CodecConformance

open Challenge.Bls12381
open Challenge.Bls12381.ProofSupport
open EvmSemantics.Crypto.Bls12381

private def nonzeroPaddingFp : ByteArray :=
  ByteArray.mk #[1] ++ Vectors.zeros 63

private def modulusFp : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded p 64

private def partialZeroOffCurveG1 : ByteArray :=
  Vectors.zeros 64 ++ EvmSemantics.Data.Bytes.natToBytesPadded 1 64

#guard (Codec.decodeG1 Vectors.generatorG1 0).isSome
#guard (Codec.decodeG2 Vectors.generatorG2 0).isSome
#guard (Codec.decodeG1Subgroup Vectors.generatorG1 0).isSome
#guard (Codec.decodeG2Subgroup Vectors.generatorG2 0).isSome

#guard match Codec.decodeG1Subgroup (Vectors.zeros Codec.g1Bytes) 0 with
  | some .infinity => true
  | _ => false
#guard match Codec.decodeG2Subgroup (Vectors.zeros Codec.g2Bytes) 0 with
  | some .infinity => true
  | _ => false

#guard (Codec.decodeG1 Vectors.nonSubgroupG1 0).isSome
#guard (Codec.decodeG2 Vectors.nonSubgroupG2 0).isSome
#guard Codec.decodeG1Subgroup Vectors.nonSubgroupG1 0 = none
#guard Codec.decodeG2Subgroup Vectors.nonSubgroupG2 0 = none
#guard match Codec.decodeG1 Vectors.nonSubgroupG1 0 with
  | some (.affine _ _) => true
  | _ => false
#guard match Codec.decodeG2 Vectors.nonSubgroupG2 0 with
  | some (.affine _ _) => true
  | _ => false

#guard Codec.decodeFp nonzeroPaddingFp 0 = none
#guard Codec.decodeFp modulusFp 0 = none
#guard Codec.decodeG1 partialZeroOffCurveG1 0 = none

#guard Codec.decodeScalar Vectors.g1Msm.input Codec.g1Bytes = some 2
#guard Codec.decodeScalar Vectors.g2Msm.input Codec.g2Bytes = some 2

#guard (Codec.decodeFp Vectors.mapFpToG1.input 0).isSome
#guard (Codec.decodeFp2 Vectors.mapFp2ToG2.input 0).isSome

end Checks.Bls12381CodecConformance
