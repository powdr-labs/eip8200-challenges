import YulParser.Compile
set_option warningAsError true

namespace Challenge.Blake2f

open YulSemantics (Block)
open YulSemantics.EVM (Op)

/-- The proof-friendly reference implementation, verbatim. Its helper layout
is intentionally part of the auditable compiler artifact. -/
def referenceSource : String := include_str "reference.yul"

def referenceSourcePath : String := "Challenge/Blake2f/Reference/reference.yul"

def referenceBlock? : Option (Block Op) :=
  match YulParser.parseSource referenceSource with
  | some (.block statements) => some statements
  | _ => none

def referenceBytecode? : Option ByteArray :=
  YulParser.compileSource referenceSource

end Challenge.Blake2f
