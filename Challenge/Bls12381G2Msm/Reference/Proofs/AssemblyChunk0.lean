import Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenAssemblyChunk0

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceAssemblyChunk0Matches : Bool :=
  toString (repr ((referenceComputedOptimizedAssembly.drop 0).take 200)) ==
    toString (repr frozenReferenceAssemblyChunk0)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
