import Challenge.Bls12381G1Add.ProofSupport.YulDialect
import Challenge.Bls12381G1Add.Reference.Source
import Challenge.Bls12381G1Add.Reference.Proofs.FrozenBlock
import YulEvmCompiler.Optimizer.Implementation.Pipeline

set_option warningAsError true

/-!
# Parsed G1ADD source program

This module connects the checked-in Yul text to the normalized AST used by
the functional proof. It intentionally contains no EVM compilation,
assembly, bytecode, or target-semantics statement.
-/

namespace Challenge.Bls12381G1Add.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op)
open YulEvmCompiler
open Challenge.Bls12381G1Add.ProofSupport.Yul

/-- Concrete evidence that parsing the checked-in source succeeds. -/
theorem referenceParseSucceeded : referenceBlock?.isSome := by
  native_decide

/-- The concrete block returned by parsing `reference.yul`. -/
def referenceParsedBlock : Block Op :=
  referenceBlock?.get referenceParseSucceeded

/-- Parser-only compatibility passes used by `yulc`. They are identities on
this source: it contains no linker placeholders, string-valued literals, or
`memoryguard` hint calls. -/
def referenceRawBlock : Block Op :=
  (YulParser.pruneLinkerBlock
    (YulParser.decodeValueStmts referenceParsedBlock)).map
      YulParser.desugarStmt

theorem referenceRawBlock_eq : referenceRawBlock = referenceParsedBlock := by
  apply YulSemantics.SyntaxEq.stmtsBeq_eq
  native_decide

/-- The semantics-preserving normalization consumed by the direct proof. -/
def referenceNormalizedBlock : Block Op :=
  @Optimizer.Normalize.normalize localDialect referenceRawBlock

/-- A readable, frozen copy of the normalized source AST. -/
def referenceCompiledBlock : Block Op := frozenReferenceBlock

/-- Finite source-text check: normalization produces exactly the AST used by
the universal functional proof. -/
theorem referenceNormalizedBlock_eq :
    referenceNormalizedBlock = referenceCompiledBlock := by
  apply YulSemantics.SyntaxEq.stmtsBeq_eq
  native_decide

/-- Normalization transports every source run; this is the only transform
between the parsed Yul and the proof-facing frozen AST. -/
theorem reference_runEquiv :
    Optimizer.RunEquivBlock localDialect referenceParsedBlock
      referenceCompiledBlock := by
  rw [← referenceNormalizedBlock_eq, referenceNormalizedBlock,
    referenceRawBlock_eq]
  exact @Optimizer.Normalize.normalize_runEquivBlock localDialect _
    referenceParsedBlock

end Challenge.Bls12381G1Add.Reference.Proofs.Compilation
