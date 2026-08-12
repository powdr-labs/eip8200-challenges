import Challenge.Bls12381G2Msm.Reference.Proofs.ComputedBlock
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk2

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceNormalizedChunk2Matches : Bool :=
  toString (repr ((computedReferenceBlock.drop 8).take 4)) ==
    toString (repr frozenReferenceBlockChunk2)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

