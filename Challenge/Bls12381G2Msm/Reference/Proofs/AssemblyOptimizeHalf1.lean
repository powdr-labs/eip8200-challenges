import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyOptimizeCore
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyEqualityChunk5
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyEqualityChunk6
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyEqualityChunk7
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyEqualityChunk8
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyEqualityChunk9

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

theorem referenceComputedAssemblyChunks_drop5 :
    referenceComputedAssemblyChunks.drop 5 =
      referenceFrozenAssemblyChunks.drop 5 := by
  simp only [referenceComputedAssemblyChunks, referenceFrozenAssemblyChunks,
    assemblyChunksOf, List.drop, List.drop_drop]
  rw [referenceAssemblyChunk5_eq,
    referenceAssemblyChunk6_eq,
    referenceAssemblyChunk7_eq,
    referenceAssemblyChunk8_eq,
    referenceAssemblyChunk9_eq]

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
