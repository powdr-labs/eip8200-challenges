import Challenge.YulProof.ModexpDialect

set_option warningAsError true

/-! Lightweight source-dialect boundary shared by executable artifacts. -/

namespace Challenge.Bls12381G1Add.ProofSupport.Yul

abbrev localDialect :=
  Challenge.YulProof.Modexp.dialect

end Challenge.Bls12381G1Add.ProofSupport.Yul
