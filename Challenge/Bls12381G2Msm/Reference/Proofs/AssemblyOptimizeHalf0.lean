import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyOptimizeCore
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyEqualityChunk0
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyEqualityChunk1
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyEqualityChunk2
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyEqualityChunk3
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyEqualityChunk4

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

theorem referenceComputedAssemblyChunks_take5 :
    referenceComputedAssemblyChunks.take 5 =
      referenceFrozenAssemblyChunks.take 5 := by
  simp only [referenceComputedAssemblyChunks, referenceFrozenAssemblyChunks,
    assemblyChunksOf, List.take, List.drop_drop]
  rw [referenceAssemblyChunk0_eq,
    referenceAssemblyChunk1_eq,
    referenceAssemblyChunk2_eq,
    referenceAssemblyChunk3_eq,
    referenceAssemblyChunk4_eq]

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
