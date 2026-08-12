import Challenge.Bls12381G1Msm.Reference.Proofs.Lowering

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

#guard toString (repr referenceInstructions) ==
  toString (repr frozenReferenceInstructions)

example : YulEvmCompiler.lowerProg referenceOptimizedAssembly =
    some referenceInstructions := referenceAssembly_lower

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.Compilation.referenceLowerSucceeded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceLowerSucceeded

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.Compilation.referenceAssembly_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceAssembly_lower
