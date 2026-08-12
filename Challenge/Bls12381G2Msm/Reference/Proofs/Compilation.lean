import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlock
import Challenge.Bls12381G2Msm.Reference.Bytecode
import YulEvmCompiler.Optimizer.Implementation.Pipeline

set_option warningAsError true

/-! Compiler front-end over the already frozen normalized G2MSM block. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op)

def referenceCompiledBlock : Block Op := frozenReferenceBlock

set_option maxRecDepth 30000 in
set_option maxHeartbeats 2000000 in
theorem referenceCompileProgramSucceeded :
    (YulEvmCompiler.compileProgram referenceCompiledBlock).isSome := by
  with_unfolding_all decide

def referenceAssembly : List YulEvmCompiler.Asm :=
  (YulEvmCompiler.compileProgram referenceCompiledBlock).get
    referenceCompileProgramSucceeded

theorem referenceCompiled_compileProgram :
    YulEvmCompiler.compileProgram referenceCompiledBlock =
      some referenceAssembly := by
  exact Option.eq_some_of_isSome referenceCompileProgramSucceeded

def referenceComputedOptimizedAssembly : List YulEvmCompiler.Asm :=
  YulEvmCompiler.optimizeAsm referenceAssembly

/-! Compact proof-facing stack-certificate data. Full assembly suffixes are
reconstructed from numeric keys only after the untrusted analyzer output has
been frozen. -/

abbrev CompactStackEntry :=
  Nat × YulEvmCompiler.FLayout × Nat × YulEvmCompiler.FLayout

def encodeStackSlot : YulEvmCompiler.FSlot → Nat
  | .word => 0
  | .ret => 1
  | .retTo label => label + 2

def decodeStackSlot : Nat → YulEvmCompiler.FSlot
  | 0 => .word
  | 1 => .ret
  | n + 2 => .retTo n

abbrev FrozenStackEntry := Nat × List Nat × Nat × List Nat

def thawStackEntry (entry : FrozenStackEntry) : CompactStackEntry :=
  (entry.1, entry.2.1.map decodeStackSlot, entry.2.2.1,
    entry.2.2.2.map decodeStackSlot)

def materializeStackCertificate (program : List YulEvmCompiler.Asm)
    (entries : List CompactStackEntry) : YulEvmCompiler.CertData where
  entries := entries.map fun entry =>
    (entry.1, program.drop (program.length - entry.1),
      entry.2.1, entry.2.2.1, entry.2.2.2)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
