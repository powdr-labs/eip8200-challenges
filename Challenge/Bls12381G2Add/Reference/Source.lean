import YulParser.Compile

set_option warningAsError true

namespace Challenge.Bls12381G2Add

open YulSemantics (Block)
open YulSemantics.EVM (Op)

/-- The proof-friendly naive G2ADD Yul implementation, verbatim. -/
def referenceSource : String := include_str "reference.yul"

def referenceSourcePath : String :=
  "Challenge/Bls12381G2Add/Reference/reference.yul"

def referenceBlock? : Option (Block Op) :=
  match YulParser.parseSource referenceSource with
  | some (.block statements) => some statements
  | _ => none

/-- Bytecode emitted by the production optimizer entry point. Retained as a
regression, but not used as the proof artifact because the optimizer's eager
inlining makes the source/refinement boundary larger. -/
def optimizedReferenceBytecode? : Option ByteArray :=
  YulParser.compileSource referenceSource

/-- Normalized source block consumed by the proof-friendly direct compiler. -/
def referenceNormalizedBlock? : Option (Block Op) := do
  let parsed ← referenceBlock?
  let decoded := YulParser.decodeValueStmts parsed
  let raw := (YulParser.pruneLinkerBlock decoded).map YulParser.desugarStmt
  return YulEvmCompiler.Optimizer.Normalize.normalize
    (D := YulSemantics.EVM.evmWithExternal
      YulSemantics.EVM.ExternalCalls.none
      YulSemantics.EVM.ExternalCreates.none) raw

/-- Bytecode emitted by the verified direct compiler from the exact normalized
source. This avoids source-optimizer equivalence plumbing and is the artifact
whose concrete EVM execution is proved. -/
def referenceBytecode? : Option ByteArray := do
  let block ← referenceNormalizedBlock?
  return YulEvmCompiler.assemble (← YulEvmCompiler.compile block)

end Challenge.Bls12381G2Add
