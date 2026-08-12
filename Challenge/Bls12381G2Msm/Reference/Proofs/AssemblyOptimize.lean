import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyOptimizeHalf0
import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyOptimizeHalf1

set_option warningAsError true

/-! Kernel-visible optimized-assembly equality composed only from opaque
half-certificate boundaries. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

private theorem referenceComputedAssemblyChunks_eq :
    referenceComputedAssemblyChunks = referenceFrozenAssemblyChunks := by
  rw [← List.take_append_drop 5 referenceComputedAssemblyChunks,
    ← List.take_append_drop 5 referenceFrozenAssemblyChunks,
    referenceComputedAssemblyChunks_take5,
    referenceComputedAssemblyChunks_drop5]

theorem referenceAssembly_optimize :
    YulEvmCompiler.optimizeAsm referenceAssembly =
      referenceOptimizedAssembly := by
  change referenceComputedOptimizedAssembly = referenceOptimizedAssembly
  rw [← referenceComputedAssemblyChunks_flatten,
    referenceComputedAssemblyChunks_eq,
    referenceFrozenAssemblyChunks_flatten]

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
