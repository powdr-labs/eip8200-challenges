import Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenAssemblyChunk6

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceAssemblyChunk6Matches : Bool :=
  toString (repr ((referenceComputedOptimizedAssembly.drop 1200).take 200)) ==
    toString (repr frozenReferenceAssemblyChunk6)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
