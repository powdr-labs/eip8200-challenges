import Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenAssemblyChunk1

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceAssemblyChunk1Matches : Bool :=
  toString (repr ((referenceComputedOptimizedAssembly.drop 200).take 200)) ==
    toString (repr frozenReferenceAssemblyChunk1)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
