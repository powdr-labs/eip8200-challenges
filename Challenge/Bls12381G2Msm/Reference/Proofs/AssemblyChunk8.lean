import Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenAssemblyChunk8

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceAssemblyChunk8Matches : Bool :=
  toString (repr ((referenceComputedOptimizedAssembly.drop 1600).take 200)) ==
    toString (repr frozenReferenceAssemblyChunk8)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
