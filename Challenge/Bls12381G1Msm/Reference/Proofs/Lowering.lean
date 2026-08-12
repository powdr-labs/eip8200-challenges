import Challenge.Bls12381G1Msm.Reference.Proofs.AssemblyOptimize
import Challenge.Bls12381G1Msm.Reference.Proofs.FrozenInstructions

set_option warningAsError true

/-! Kernel-checked label lowering for the frozen G1MSM assembly. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

open YulEvmCompiler

set_option maxRecDepth 50000 in
theorem referenceLowerSucceeded :
    (lowerProg referenceOptimizedAssembly).isSome := by
  with_unfolding_all decide

def referenceInstructions : List Instr :=
  (lowerProg referenceOptimizedAssembly).get referenceLowerSucceeded

theorem referenceAssembly_lower :
    lowerProg referenceOptimizedAssembly = some referenceInstructions := by
  exact Option.eq_some_of_isSome referenceLowerSucceeded

end Challenge.Bls12381G1Msm.Reference.Proofs.Compilation
