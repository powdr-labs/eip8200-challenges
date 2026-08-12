import Challenge.Bls12381G2Msm.Reference.Proofs.ComputedBlock
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk4

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceNormalizedChunk4Matches : Bool :=
  toString (repr ((computedReferenceBlock.drop 16).take 4)) ==
    toString (repr frozenReferenceBlockChunk4)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

