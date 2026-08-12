import Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenAssemblyChunk4

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceAssemblyChunk4Matches : Bool :=
  toString (repr ((referenceComputedOptimizedAssembly.drop 800).take 200)) ==
    toString (repr frozenReferenceAssemblyChunk4)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
