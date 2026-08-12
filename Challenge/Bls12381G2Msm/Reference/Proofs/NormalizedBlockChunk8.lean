import Challenge.Bls12381G2Msm.Reference.Proofs.ComputedBlock
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk8

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceNormalizedChunk8Matches : Bool :=
  toString (repr ((computedReferenceBlock.drop 32).take 4)) ==
    toString (repr frozenReferenceBlockChunk8)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

