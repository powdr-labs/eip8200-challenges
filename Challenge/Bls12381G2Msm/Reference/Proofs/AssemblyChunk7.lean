import Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenAssemblyChunk7

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceAssemblyChunk7Matches : Bool :=
  toString (repr ((referenceComputedOptimizedAssembly.drop 1400).take 200)) ==
    toString (repr frozenReferenceAssemblyChunk7)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
