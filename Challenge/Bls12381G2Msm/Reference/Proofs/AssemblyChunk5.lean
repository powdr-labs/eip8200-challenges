import Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenAssemblyChunk5

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceAssemblyChunk5Matches : Bool :=
  toString (repr ((referenceComputedOptimizedAssembly.drop 1000).take 200)) ==
    toString (repr frozenReferenceAssemblyChunk5)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
