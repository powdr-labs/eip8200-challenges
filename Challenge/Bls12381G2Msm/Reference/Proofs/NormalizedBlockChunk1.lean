import Challenge.Bls12381G2Msm.Reference.Proofs.ComputedBlock
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk1

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceNormalizedChunk1Matches : Bool :=
  toString (repr ((computedReferenceBlock.drop 4).take 4)) ==
    toString (repr frozenReferenceBlockChunk1)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

