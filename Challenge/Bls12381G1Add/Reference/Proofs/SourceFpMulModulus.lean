import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulStores

set_option warningAsError true

/-! # Frozen G1ADD `fpMul` modulus store -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

/-- The source's ninth body statement invokes `storeModulus` at offset 1217,
completing the exact 241-byte MODEXP input. -/
theorem exec_fpMulModulus (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 57 fpMulBodyFuns
      (fpMulProductEnv ahi alo bhi blo)
      (fpMulPreModulusState yst ahi alo bhi blo) fpMulStmt8 =
    .ok (fpMulProductEnv ahi alo bhi blo,
      fpMulInputState yst ahi alo bhi blo, .normal) := by
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
