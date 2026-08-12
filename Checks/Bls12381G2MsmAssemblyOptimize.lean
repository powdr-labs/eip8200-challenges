import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyOptimize

set_option warningAsError true

open Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

example : YulEvmCompiler.optimizeAsm referenceAssembly =
    referenceOptimizedAssembly := referenceAssembly_optimize

/-- info: 'Challenge.Bls12381G2Msm.Reference.Proofs.Compilation.referenceAssembly_optimize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceAssembly_optimize
