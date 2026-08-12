import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulStep0

set_option warningAsError true

/-! # Frozen G1ADD `fpMul` input stores -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

/-- The seven direct stores construct the exact MODEXP header, product, and
exponent-prefix state while preserving the helper's variable environment. -/
theorem exec_fpMulStores (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 65 fpMulBodyFuns
      (fpMulProductEnv ahi alo bhi blo) yst
      [fpMulStmt1, fpMulStmt2, fpMulStmt3, fpMulStmt4,
        fpMulStmt5, fpMulStmt6, fpMulStmt7] =
    .ok (fpMulProductEnv ahi alo bhi blo,
      fpMulPreModulusState yst ahi alo bhi blo, .normal) := by
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
