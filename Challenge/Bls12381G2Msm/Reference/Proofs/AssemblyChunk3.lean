import Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenAssemblyChunk3

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceAssemblyChunk3Matches : Bool :=
  toString (repr ((referenceComputedOptimizedAssembly.drop 600).take 200)) ==
    toString (repr frozenReferenceAssemblyChunk3)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
