import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpMulBody

set_option warningAsError true

/-! Frozen G2MSM `fpMul` execution endpoint. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem eval_fpMul (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68
      [hoist Challenge.EvmProof.modexpExec.toDialect
        Compilation.referenceCompiledBlock]
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x009" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [(fpMulResult yst ahi alo bhi blo).1,
      (fpMulResult yst ahi alo bhi blo).2]
      (fpMulFinalState yst ahi alo bhi blo)) := by
  have h := eval_fpMul_of_body ahi alo bhi blo yst
    (fpMulFinalState yst ahi alo bhi blo)
    (fpMulBodyResultEnv yst ahi alo bhi blo)
    (exec_fpMulBody ahi alo bhi blo yst)
  rw [fpMulBodyResultEnv_hi, fpMulBodyResultEnv_lo] at h
  exact h

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
