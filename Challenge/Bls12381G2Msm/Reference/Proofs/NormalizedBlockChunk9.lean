import Challenge.Bls12381G2Msm.Reference.Proofs.ComputedBlock
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk9

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceNormalizedChunk9Matches : Bool :=
  toString (repr ((computedReferenceBlock.drop 36).take 4)) ==
    toString (repr frozenReferenceBlockChunk9)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

