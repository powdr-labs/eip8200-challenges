import Challenge.Bls12381G2Add.Reference
import Challenge.Bls12381G2Add.Scorer

set_option warningAsError true

namespace Checks.Bls12381G2AddReferenceRuntime

open Challenge.Bls12381G2Add
open Challenge.Bls12381.ProofSupport

def compiledReference : ByteArray := referenceBytecode

private def ok : Challenge.Bls12381.Scorer.Outcome → Bool
  | .ok _ => true
  | _ => false

#guard ok (Challenge.Bls12381.Scorer.score Scorer.config
  compiledReference Challenge.Bls12381.Vectors.g2Add.input)

#guard ok (Challenge.Bls12381.Scorer.score Scorer.config
  compiledReference Challenge.Bls12381.Vectors.g2AddNonSubgroup.input)

#guard ok (Challenge.Bls12381.Scorer.score Scorer.config
  compiledReference (Challenge.Bls12381.Vectors.zeros 512))

#guard ok (Challenge.Bls12381.Scorer.score Scorer.config
  compiledReference .empty)

#guard ok (Challenge.Bls12381.Scorer.score Scorer.config
  compiledReference (Challenge.Bls12381.Vectors.zeros 511))

#guard ok (Challenge.Bls12381.Scorer.score Scorer.config
  compiledReference (Challenge.Bls12381.Vectors.zeros 513))

#guard ok (Challenge.Bls12381.Scorer.score Scorer.config
  compiledReference (Challenge.Bls12381.Vectors.generatorG2 ++
    Challenge.Bls12381.Vectors.generatorG2))

private def generatorPoint : EvmSemantics.Crypto.Bls12381.G2Point :=
  (Codec.decodeG2 Challenge.Bls12381.Vectors.generatorG2 0).getD .infinity

private def oppositeInput : ByteArray :=
  Challenge.Bls12381.Vectors.generatorG2 ++
    Codec.encodeG2 (G2Affine.toWire (G2Affine.neg (G2Affine.ofWire generatorPoint)))

#guard ok (Challenge.Bls12381.Scorer.score Scorer.config
  compiledReference oppositeInput)

private def offCurveInput : ByteArray :=
  Codec.encodeG2 (.affine 1 1) ++ Challenge.Bls12381.Vectors.zeros Codec.g2Bytes

#guard ok (Challenge.Bls12381.Scorer.score Scorer.config
  compiledReference offCurveInput)

#guard ok (Challenge.Bls12381.Scorer.score Scorer.config compiledReference
  (Challenge.Bls12381.Vectors.p2 ++ Challenge.Bls12381.Vectors.generatorG2))

#guard ok (Challenge.Bls12381.Scorer.score Scorer.config compiledReference
  (Challenge.Bls12381.Vectors.p2 ++ Challenge.Bls12381.Vectors.p2))

#guard ok (Challenge.Bls12381.Scorer.score Scorer.config compiledReference
  (Challenge.Bls12381.Vectors.zeros 256 ++ Challenge.Bls12381.Vectors.generatorG2))

#guard ok (Challenge.Bls12381.Scorer.score Scorer.config compiledReference
  (Challenge.Bls12381.Vectors.generatorG2 ++ Challenge.Bls12381.Vectors.zeros 256))

private def noncanonicalInput : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded EvmSemantics.Crypto.Bls12381.p 64 ++
    Challenge.Bls12381.Vectors.zeros 448

#guard ok (Challenge.Bls12381.Scorer.score Scorer.config compiledReference
  noncanonicalInput)

end Checks.Bls12381G2AddReferenceRuntime
