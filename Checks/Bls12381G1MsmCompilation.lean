import Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

#guard toString (repr referenceParsedRawBlock) ==
  toString (repr referenceRawBlock)
#guard toString (repr referenceComputedOptimizedBlock) ==
  toString (repr referenceCompiledBlock)
#guard (YulEvmCompiler.compile referenceCompiledBlock).isNone
#guard (YulEvmCompiler.compile referenceCleanedLayoutBlock).isSome
#guard toString (repr referenceCleanedLayoutBlock) ==
  toString (repr referenceBackendBlock)
#guard toString (repr referenceComputedAssembly) ==
  toString (repr referenceAssembly)
#guard toString (repr referenceComputedOptimizedAssembly) ==
  toString (repr referenceOptimizedAssembly)
#guard referenceCompile?.isSome
#guard referenceCompiledBytecode? = some Challenge.Bls12381G1Msm.referenceBytecode
