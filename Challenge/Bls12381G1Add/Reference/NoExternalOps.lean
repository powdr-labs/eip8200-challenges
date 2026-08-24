import Challenge.Bls12381G1Add.Reference.Source
import Challenge.YulProof.NoExternalOps

set_option warningAsError true

/-! # Source-only no-external-operation certificate for G1ADD -/

namespace Challenge.Bls12381G1Add.Reference

/-- The parser succeeds on the checked-in G1ADD source and its complete AST
contains no `call`, `callcode`, `delegatecall`, `staticcall`, `create`, or
`create2` builtin. -/
theorem referenceParsed_noExternalOps :
    Challenge.YulProof.NoExternalOps.ParsedHolds referenceBlock? := by
  native_decide

end Challenge.Bls12381G1Add.Reference
