import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyChunk0
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyChunk1
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyChunk2
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyChunk3
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyChunk4
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyChunk5
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyChunk6
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyChunk7
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyChunk8
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyChunk9

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def referenceOptimizedAssembly : List YulEvmCompiler.Asm :=
  frozenReferenceAssemblyChunk0 ++
    frozenReferenceAssemblyChunk1 ++
    frozenReferenceAssemblyChunk2 ++
    frozenReferenceAssemblyChunk3 ++
    frozenReferenceAssemblyChunk4 ++
    frozenReferenceAssemblyChunk5 ++
    frozenReferenceAssemblyChunk6 ++
    frozenReferenceAssemblyChunk7 ++
    frozenReferenceAssemblyChunk8 ++
    frozenReferenceAssemblyChunk9

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
