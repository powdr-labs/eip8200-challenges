import YulParser.Compile
import YulEvmCompiler.Optimizer.Implementation.Pipeline

set_option warningAsError true

namespace Challenge.Ripemd160

open YulSemantics (Block)
open YulSemantics.EVM (Op)
open YulSemantics.EVM (ExternalCalls ExternalCreates evmWithExternal)
open YulEvmCompiler

/-- The reference implementation, verbatim. -/
def referenceSource : String := include_str "reference.yul"

/-- Where that file lives, for executable tooling. -/
def referenceSourcePath : String := "Challenge/Ripemd160/Reference/reference.yul"

/-- The parsed reference source. -/
def referenceBlock? : Option (Block Op) :=
  match YulParser.parseSource referenceSource with
  | some (.block statements) => some statements
  | _ => none

/-- Bytecode emitted by the pinned verified Yul compiler. -/
def referenceBytecode? : Option ByteArray :=
  match referenceBlock? with
  | none => none
  | some block =>
    let normalized : Block Op := @Optimizer.Normalize.normalize
      (evmWithExternal ExternalCalls.none ExternalCreates.none) block
    let optimized := (Optimizer.optimizerPipeline
      (calls := ExternalCalls.none) (creates := ExternalCreates.none)).run normalized
    match compile optimized with
    | some is => some (assemble is)
    | none => none

end Challenge.Ripemd160
