import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulBody

set_option warningAsError true

/-! Relational call semantics of the frozen G1MSM `fpMul` helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_fpMul_of_args {funs V st argState args} (ahi alo bhi blo : U256)
    (hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V st args
      (.vals [ahi, alo, bhi, blo] argState))
    (hlookup : lookupFun funs "\x009" = some (fpMulDecl, sourceFuns)) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.call "\x009" args)
      (.vals [(fpMulResult argState ahi alo bhi blo).1,
        (fpMulResult argState ahi alo bhi blo).2]
        (fpMulFinalState argState ahi alo bhi blo)) := by
  have hcall : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.call "\x009" args)
      (.vals
        [(VEnv.get (fpMulBodyResultEnv argState ahi alo bhi blo) "\x0077").getD 0,
         (VEnv.get (fpMulBodyResultEnv argState ahi alo bhi blo) "\x0078").getD 0]
        (fpMulFinalState argState ahi alo bhi blo)) :=
    Step.callOk hargs hlookup rfl (step_fpMulBody ahi alo bhi blo argState)
      (Or.inl rfl)
  rw [fpMulBodyResultEnv_hi, fpMulBodyResultEnv_lo] at hcall
  exact hcall

theorem step_fpMul (ahi alo bhi blo : U256) (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect sourceFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x009" [.var "ahi", .var "alo", .var "bhi", .var "blo"])
      (.vals [(fpMulResult yst ahi alo bhi blo).1,
        (fpMulResult yst ahi alo bhi blo).2]
        (fpMulFinalState yst ahi alo bhi blo)) := by
  have hhi : EvalExpr Challenge.EvmProof.modexpExec.toDialect sourceFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.var "ahi") (.vals [ahi] yst) := Step.var rfl
  have halo : EvalExpr Challenge.EvmProof.modexpExec.toDialect sourceFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.var "alo") (.vals [alo] yst) := Step.var rfl
  have hbhi : EvalExpr Challenge.EvmProof.modexpExec.toDialect sourceFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.var "bhi") (.vals [bhi] yst) := Step.var rfl
  have hblo : EvalExpr Challenge.EvmProof.modexpExec.toDialect sourceFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.var "blo") (.vals [blo] yst) := Step.var rfl
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect sourceFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      [.var "ahi", .var "alo", .var "bhi", .var "blo"]
      (.vals [ahi, alo, bhi, blo] yst) :=
    Step.argsCons (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil
      hblo) hbhi) halo) hhi
  exact step_fpMul_of_args ahi alo bhi blo hargs lookup_fpMul

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
