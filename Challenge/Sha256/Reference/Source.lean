import YulParser.Compile

set_option warningAsError true

/-!
# Reference Yul artifact

The human-readable reference implementation and the parser/compiler values
derived from it.  Correctness proofs live separately under `Reference/Proofs`.
-/

namespace Challenge.Sha256

open YulSemantics (Block)
open YulSemantics.EVM (Op)

/-- The reference implementation, verbatim. -/
def referenceSource : String := include_str "reference.yul"

/-- Where that file lives, for the scorer's default argument. -/
def referenceSourcePath : String := "Challenge/Sha256/Reference/reference.yul"

/-- The reference AST produced by the verified parser. -/
def referenceBlock? : Option (Block Op) :=
  match YulParser.parseSource referenceSource with
  | some (.block statements) => some statements
  | _ => none

/-- The bytecode produced by the verified Yul compiler. -/
def referenceBytecode? : Option ByteArray :=
  YulParser.compileSourceWithBackend referenceSource [] .classic

end Challenge.Sha256
