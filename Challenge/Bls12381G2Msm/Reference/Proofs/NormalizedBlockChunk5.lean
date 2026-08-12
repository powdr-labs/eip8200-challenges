import Challenge.Bls12381G2Msm.Reference.Proofs.ComputedBlock
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk5

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceNormalizedChunk5Matches : Bool :=
  toString (repr ((computedReferenceBlock.drop 20).take 4)) ==
    toString (repr frozenReferenceBlockChunk5)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

