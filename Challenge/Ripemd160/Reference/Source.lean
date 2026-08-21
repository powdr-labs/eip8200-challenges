import YulParser.Compile

set_option warningAsError true

namespace Challenge.Ripemd160

open YulSemantics (Block)
open YulSemantics.EVM (Op)

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
  YulParser.compileSourceWithBackend referenceSource [] .classic

end Challenge.Ripemd160
