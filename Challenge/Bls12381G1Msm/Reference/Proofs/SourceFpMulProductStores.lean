import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulProductDefs

set_option warningAsError true

/-! Executable certificate for the six direct product stores in `fpMul`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem exec_fpMulProductStores (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 64
      ([] :: fpMulBodyFuns) (fpMulProductEnv ahi alo bhi blo) yst
      fpMulProductStores =
    .ok (fpMulProductEnv ahi alo bhi blo,
      fpMulProductState yst ahi alo bhi blo, .normal) := by
  rw [Interp.execStmts.eq_def]
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
