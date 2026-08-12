import Challenge.Bls12381G2Msm.Reference.Proofs.Lowering

set_option warningAsError true

open Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

example : (YulEvmCompiler.lowerProg referenceOptimizedAssembly).isSome :=
  referenceLowerSucceeded

example : YulEvmCompiler.lowerProg referenceOptimizedAssembly =
    some referenceInstructions :=
  referenceAssembly_lower
