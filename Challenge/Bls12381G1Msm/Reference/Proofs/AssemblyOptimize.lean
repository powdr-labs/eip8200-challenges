import Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

set_option warningAsError true

/-! Kernel-checked peephole boundary for the frozen G1MSM assembly. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

theorem referenceAssembly_optimize :
    YulEvmCompiler.optimizeAsm referenceAssembly =
      referenceOptimizedAssembly := by
  set_option maxRecDepth 20000 in
    with_unfolding_all decide

end Challenge.Bls12381G1Msm.Reference.Proofs.Compilation
