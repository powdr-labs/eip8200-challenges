import Challenge.Bls12381G2Msm.Reference.Proofs.ComputedBlock
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk7

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceNormalizedChunk7Matches : Bool :=
  toString (repr ((computedReferenceBlock.drop 28).take 4)) ==
    toString (repr frozenReferenceBlockChunk7)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

