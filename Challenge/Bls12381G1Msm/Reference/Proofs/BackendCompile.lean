import Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

set_option warningAsError true

/-! Kernel-checked source-backend compilation at the frozen block boundary. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

theorem referenceBackendBlock_compileProgram :
    YulEvmCompiler.compileProgram referenceBackendBlock =
      some referenceAssembly := by
  set_option maxRecDepth 20000 in
    with_unfolding_all decide

end Challenge.Bls12381G1Msm.Reference.Proofs.Compilation
