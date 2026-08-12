import Challenge.Bls12381G1Add.ProofSupport.YulDialect
import Challenge.Bls12381G1Add.Reference.Bytecode
import Challenge.Bls12381G1Add.Reference.Proofs.FrozenBlock
import Challenge.Bls12381G1Add.Reference.Proofs.FrozenAssembly
import Challenge.EvmProof.StackCertificate
import YulEvmCompiler.Optimizer.Implementation.Pipeline

set_option warningAsError true

/-!
# Frozen G1ADD source/compiler certificate

This module names the exact normalized and optimized Yul block whose verified
compiler output is the frozen 1723-byte runtime.  It is an ordinary checked
source/assembly equality; it does not use a certified-artifact builder.
-/

namespace Challenge.Bls12381G1Add.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op ExternalCreates)
open YulEvmCompiler
open Challenge.Bls12381G1Add.ProofSupport.Yul

def referenceParsedBlock : Block Op :=
  referenceBlock?.getD []

def referencePrunedBlock : Block Op :=
  YulParser.pruneLinkerBlock
    (YulParser.decodeValueStmts referenceParsedBlock)

def referenceRawBlock : Block Op :=
  referencePrunedBlock.map YulParser.desugarStmt

def referenceParsedCompiledBlock : Block Op :=
  @Optimizer.Normalize.normalize localDialect referenceRawBlock

/-- Exact normalized block accepted by the verified backend.  This is frozen
as ordinary Lean data so compilation can reduce in the kernel; the source
parser equivalence remains an executable regression check. -/
def referenceCompiledBlock : Block Op := frozenReferenceBlock

/-- Concrete evidence that the transparent source-to-assembly phase accepts
the frozen block. -/
theorem referenceCompileProgramSucceeded :
    (compileProgram referenceCompiledBlock).isSome := by
  set_option maxRecDepth 10000 in
    with_unfolding_all decide

/-- The exact labeled assembly produced by the transparent first phase. -/
def referenceAssembly : List Asm :=
  (compileProgram referenceCompiledBlock).get referenceCompileProgramSucceeded

theorem referenceCompiled_compileProgram :
    compileProgram referenceCompiledBlock = some referenceAssembly := by
  exact Option.eq_some_of_isSome referenceCompileProgramSucceeded

/-- Assembly computed from the frozen normalized block, retained for the
source/compiler regression check. -/
def referenceComputedOptimizedAssembly : List Asm :=
  optimizeAsm referenceAssembly

/-- Exact peephole-optimized labeled assembly used by byte-level lowering. -/
def referenceOptimizedAssembly : List Asm := frozenReferenceAssembly

/-- Kernel-checked equality from the frozen normalized source block through
the transparent source compiler and peephole pass to the explicit assembly. -/
theorem referenceComputedOptimizedAssembly_eq :
    referenceComputedOptimizedAssembly = referenceOptimizedAssembly := by
  set_option maxRecDepth 20000 in
    with_unfolding_all decide

/-- Compact, proof-facing form of a stack-layout certificate entry.  Program
suffixes are reconstructed from their length instead of being duplicated in
the frozen data. -/
abbrev CompactStackEntry :=
  Challenge.EvmProof.StackCertificate.CompactStackEntry

/-- Stable numeric encoding used only to keep the frozen certificate compact. -/
abbrev encodeStackSlot : FSlot → Nat :=
  Challenge.EvmProof.StackCertificate.encodeStackSlot

abbrev decodeStackSlot : Nat → FSlot :=
  Challenge.EvmProof.StackCertificate.decodeStackSlot

abbrev FrozenStackEntry :=
  Challenge.EvmProof.StackCertificate.FrozenStackEntry

def thawStackEntry (entry : FrozenStackEntry) : CompactStackEntry :=
  (entry.1, entry.2.1.map decodeStackSlot, entry.2.2.1,
    entry.2.2.2.map decodeStackSlot)

def materializeStackCertificate (program : List Asm)
    (entries : List CompactStackEntry) : CertData where
  entries := entries.map fun entry =>
    (entry.1, program.drop (program.length - entry.1),
      entry.2.1, entry.2.2.1, entry.2.2.2)

end Challenge.Bls12381G1Add.Reference.Proofs.Compilation
