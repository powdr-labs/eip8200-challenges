import Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenAssemblyChunk9

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceAssemblyChunk9Matches : Bool :=
  toString (repr ((referenceComputedOptimizedAssembly.drop 1800).take 200)) ==
    toString (repr frozenReferenceAssemblyChunk9)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
