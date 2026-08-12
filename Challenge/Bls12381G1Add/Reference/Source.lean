import YulParser.Compile

set_option warningAsError true

namespace Challenge.Bls12381G1Add

open YulSemantics (Block)
open YulSemantics.EVM (Op)

/--
The proof-friendly naive G1ADD Yul implementation, verbatim, including its
exact fixed MODEXP call budgets.
-/
def referenceSource : String := include_str "reference.yul"

def referenceSourcePath : String :=
  "Challenge/Bls12381G1Add/Reference/reference.yul"

def referenceBlock? : Option (Block Op) :=
  match YulParser.parseSource referenceSource with
  | some (.block statements) => some statements
  | _ => none

/-- Bytecode emitted by the verified Yul compiler from `referenceSource`. -/
def referenceBytecode? : Option ByteArray :=
  YulParser.compileSource referenceSource

end Challenge.Bls12381G1Add
