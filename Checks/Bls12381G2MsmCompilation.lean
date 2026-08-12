import Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenAssembly

set_option warningAsError true

open Challenge.Bls12381G2Msm
open Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

#guard referenceBlock?.isSome
#guard referenceNormalizedBlock?.map List.length = some 41
#guard frozenReferenceBlock.length = 41

#guard referenceNormalizedChunk0Matches
#guard referenceNormalizedChunk1Matches
#guard referenceNormalizedChunk2Matches
#guard referenceNormalizedChunk3Matches
#guard referenceNormalizedChunk4Matches
#guard referenceNormalizedChunk5Matches
#guard referenceNormalizedChunk6Matches
#guard referenceNormalizedChunk7Matches
#guard referenceNormalizedChunk8Matches
#guard referenceNormalizedChunk9Matches
#guard referenceNormalizedChunk10Matches

example : (YulEvmCompiler.compileProgram referenceCompiledBlock).isSome :=
  referenceCompileProgramSucceeded

example : YulEvmCompiler.compileProgram referenceCompiledBlock =
    some referenceAssembly :=
  referenceCompiled_compileProgram
#guard referenceAssemblyChunk0Matches
#guard referenceAssemblyChunk1Matches
#guard referenceAssemblyChunk2Matches
#guard referenceAssemblyChunk3Matches
#guard referenceAssemblyChunk4Matches
#guard referenceAssemblyChunk5Matches
#guard referenceAssemblyChunk6Matches
#guard referenceAssemblyChunk7Matches
#guard referenceAssemblyChunk8Matches
#guard referenceAssemblyChunk9Matches
