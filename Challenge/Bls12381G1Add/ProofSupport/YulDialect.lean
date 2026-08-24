import Challenge.YulProof.ClosedEvmDialect

set_option warningAsError true

/-! Lightweight source-dialect boundary shared by executable artifacts. -/

namespace Challenge.Bls12381G1Add.ProofSupport.Yul

abbrev localDialect :=
  Challenge.YulProof.ClosedEvm.dialect

end Challenge.Bls12381G1Add.ProofSupport.Yul
