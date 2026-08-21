import YulParser.Compile
set_option warningAsError true

namespace Challenge.Modexp

open YulSemantics (Block)
open YulSemantics.EVM (Op)

def referenceSource : String := include_str "reference.yul"

def referenceSourcePath : String := "Challenge/Modexp/Reference/reference.yul"

def referenceBlock? : Option (Block Op) :=
  match YulParser.parseSource referenceSource with
  | some (.block statements) => some statements
  | _ => none

def referenceBytecode? : Option ByteArray :=
  YulParser.compileSourceWithBackend referenceSource [] .classic

end Challenge.Modexp
