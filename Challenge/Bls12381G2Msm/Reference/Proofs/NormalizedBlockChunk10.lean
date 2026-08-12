import Challenge.Bls12381G2Msm.Reference.Proofs.ComputedBlock
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk10

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceNormalizedChunk10Matches : Bool :=
  toString (repr ((computedReferenceBlock.drop 40).take 4)) ==
    toString (repr frozenReferenceBlockChunk10)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

