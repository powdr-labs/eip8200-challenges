import Challenge.Bls12381G2Add.Reference.Proofs.Compilation

set_option warningAsError true

/-! Checked G2ADD assembly lowering. -/

namespace Challenge.Bls12381G2Add.Reference.Proofs.Compilation

open YulEvmCompiler

set_option maxRecDepth 30000 in
theorem referenceLowerSucceeded :
    (lowerProg referenceOptimizedAssembly).isSome := by
  with_unfolding_all decide

def referenceInstructions : List Instr :=
  (lowerProg referenceOptimizedAssembly).get referenceLowerSucceeded

theorem referenceAssembly_lower :
    lowerProg referenceOptimizedAssembly = some referenceInstructions := by
  exact Option.eq_some_of_isSome referenceLowerSucceeded

end Challenge.Bls12381G2Add.Reference.Proofs.Compilation

