import Challenge.Bls12381G2Msm.Reference.Proofs.ComputedBlock
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk0

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceNormalizedChunk0Matches : Bool :=
  toString (repr (computedReferenceBlock.take 4)) ==
    toString (repr frozenReferenceBlockChunk0)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
