import YulParser.Compile

set_option warningAsError true

namespace Challenge.Bls12381G2Msm

open YulSemantics (Block)
open YulSemantics.EVM (Op)

/-- Proof-friendly naive G2MSM Yul implementation. -/
def referenceSource : String := include_str "reference.yul"

def referenceSourcePath : String :=
  "Challenge/Bls12381G2Msm/Reference/reference.yul"

def referenceBlock? : Option (Block Op) :=
  match YulParser.parseSource referenceSource with
  | some (.block statements) => some statements
  | _ => none

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
source. -/
def referenceBytecode? : Option ByteArray := do
  let block ← referenceNormalizedBlock?
  return YulEvmCompiler.assemble (← YulEvmCompiler.compile block)

end Challenge.Bls12381G2Msm
