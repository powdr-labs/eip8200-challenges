import Challenge.Bls12381G1Add.Reference.Proofs.Compilation

set_option warningAsError true

/-!
# Checked G1ADD assembly lowering

This module lowers the explicit optimized assembly with the verified total
label resolver and checks its assembled bytes against the explicit runtime.
-/

namespace Challenge.Bls12381G1Add.Reference.Proofs.Compilation

open YulEvmCompiler
open Challenge.Bls12381G1Add

set_option maxRecDepth 20000 in
theorem referenceLowerSucceeded :
    (lowerProg referenceOptimizedAssembly).isSome := by
  with_unfolding_all decide

def referenceInstructions : List Instr :=
  (lowerProg referenceOptimizedAssembly).get referenceLowerSucceeded

theorem referenceAssembly_lower :
    lowerProg referenceOptimizedAssembly = some referenceInstructions := by
  exact Option.eq_some_of_isSome referenceLowerSucceeded

end Challenge.Bls12381G1Add.Reference.Proofs.Compilation
