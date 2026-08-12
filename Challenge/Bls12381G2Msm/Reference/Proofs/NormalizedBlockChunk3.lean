import Challenge.Bls12381G2Msm.Reference.Proofs.ComputedBlock
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk3

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceNormalizedChunk3Matches : Bool :=
  toString (repr ((computedReferenceBlock.drop 12).take 4)) ==
    toString (repr frozenReferenceBlockChunk3)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

