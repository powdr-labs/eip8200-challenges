import Challenge.Bls12381G1Msm.Reference.Bytecode
import Challenge.Bls12381G1Msm.Reference.Proofs.FrozenRawBlock
import Challenge.Bls12381G1Msm.Reference.Proofs.FrozenOptimizedBlock
import Challenge.Bls12381G1Msm.Reference.Proofs.FrozenBackendBlock
import Challenge.Bls12381G1Msm.Reference.Proofs.FrozenAssembly
import YulEvmCompiler.Optimizer.Implementation.Pipeline

set_option warningAsError true

/-!
# G1MSM source/compiler boundary

This module exposes only the exact raw block and optimized compiler candidate.
Arithmetic and MSM semantics remain outside this executable boundary.
-/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op ExternalCalls ExternalCreates)
open YulEvmCompiler

def referenceParsedBlock : Block Op :=
  Challenge.Bls12381G1Msm.referenceBlock?.getD []

def referenceParsedRawBlock : Block Op :=
  YulParser.pruneLinkerBlock (YulParser.decodeValueStmts referenceParsedBlock)

/-- Proof-facing raw source block. The parser equality is kept as a separate
executable regression because the parser itself is a partial definition. -/
def referenceRawBlock : Block Op := frozenReferenceRawBlock

def referenceNormalizedBlock : Block Op :=
  Optimizer.Normalize.normalize
    (D := YulSemantics.EVM.evmWithExternal ExternalCalls.none ExternalCreates.none)
    referenceRawBlock

def referenceComputedOptimizedBlock : Block Op :=
  (Optimizer.optimizerPipeline
    (calls := ExternalCalls.none) (creates := ExternalCreates.none)).run
      referenceNormalizedBlock

/-- Proof-facing optimized source block. Optimizer equality is retained as a
separate executable regression rather than unfolded in semantic proofs. -/
def referenceCompiledBlock : Block Op := frozenReferenceOptimizedBlock

def referenceCleanedLayoutBlock : Block Op :=
  Optimizer.cleanupAfterLayoutBlock
    (calls := ExternalCalls.none) (creates := ExternalCreates.none)
    (Optimizer.stackLayoutBlock referenceCompiledBlock)

def referenceLayoutBlock : Block Op :=
  Optimizer.stackLayoutBlock referenceCompiledBlock

/-- Proof-facing cleaned stack-layout block accepted by the backend. -/
def referenceBackendBlock : Block Op := frozenReferenceBackendBlock

def referenceComputedAssembly : List Asm :=
  (compileProgram referenceBackendBlock).getD []

def referenceAssembly : List Asm := frozenReferenceAssembly

def referenceComputedOptimizedAssembly : List Asm :=
  optimizeAsm referenceAssembly

def referenceOptimizedAssembly : List Asm := frozenReferenceOptimizedAssembly

/-- Exact first successful optimized fallback used by `compileSource`. -/
def referenceCompile? : Option (List Instr) := compile referenceBackendBlock

def referenceCompiledBytecode? : Option ByteArray :=
  referenceCompile?.map assemble

/-! Compact proof-facing stack-certificate data. Full assembly suffixes are
reconstructed from their lengths instead of duplicated in the payload. -/

abbrev CompactStackEntry := Nat × FLayout × Nat × FLayout

def encodeStackSlot : FSlot → Nat
  | .word => 0
  | .ret => 1
  | .retTo label => label + 2

def decodeStackSlot : Nat → FSlot
  | 0 => .word
  | 1 => .ret
  | n + 2 => .retTo n

abbrev FrozenStackEntry := Nat × List Nat × Nat × List Nat

def thawStackEntry (entry : FrozenStackEntry) : CompactStackEntry :=
  (entry.1, entry.2.1.map decodeStackSlot, entry.2.2.1,
    entry.2.2.2.map decodeStackSlot)

def materializeStackCertificate (program : List Asm)
    (entries : List CompactStackEntry) : CertData where
  entries := entries.map fun entry =>
    (entry.1, program.drop (program.length - entry.1), entry.2.1,
      entry.2.2.1, entry.2.2.2)

end Challenge.Bls12381G1Msm.Reference.Proofs.Compilation
