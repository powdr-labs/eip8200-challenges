import Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenAssemblyChunk2

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceAssemblyChunk2Matches : Bool :=
  toString (repr ((referenceComputedOptimizedAssembly.drop 400).take 200)) ==
    toString (repr frozenReferenceAssemblyChunk2)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
