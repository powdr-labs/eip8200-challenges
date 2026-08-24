import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulBody

set_option warningAsError true
set_option maxHeartbeats 100000

/-! # Opaque native `fpMul` result components -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem fpMulSourceBodyResultEnv_eq (ahi alo bhi blo : U256) :
    fpMulSourceBodyResultEnv ahi alo bhi blo =
      fpMulReturnEnvWith ahi alo bhi blo
        (fpReduceProductValue (fullMulValue ahi alo bhi blo)).hi
        (fpReduceProductValue (fullMulValue ahi alo bhi blo)).lo := by
  simpa only [fpMulSourceBodyResultEnv, fpMulSourceAssignedEnv,
    fpMulAssignedEnvWith] using
      restore_fpMulAssignedEnvWith ahi alo bhi blo
        (fpReduceProductValue (fullMulValue ahi alo bhi blo)).hi
        (fpReduceProductValue (fullMulValue ahi alo bhi blo)).lo

theorem fpMulResultValue_hi_graph (ahi alo bhi blo : U256) :
    (fpMulResultValue ahi alo bhi blo).1 =
      (fpMulResultGraph ahi alo bhi blo).hi :=
  congrArg Prod.fst (fpMulResultValue_spec ahi alo bhi blo)

theorem fpMulResultValue_lo_graph (ahi alo bhi blo : U256) :
    (fpMulResultValue ahi alo bhi blo).2 =
      (fpMulResultGraph ahi alo bhi blo).lo :=
  congrArg Prod.snd (fpMulResultValue_spec ahi alo bhi blo)

theorem fpMulResult_hi_graph (yst : EvmState) (ahi alo bhi blo : U256) :
    (fpMulResult yst ahi alo bhi blo).1 =
      (fpMulResultGraph ahi alo bhi blo).hi :=
  fpMulResultValue_hi_graph ahi alo bhi blo

theorem fpMulResult_lo_graph (yst : EvmState) (ahi alo bhi blo : U256) :
    (fpMulResult yst ahi alo bhi blo).2 =
      (fpMulResultGraph ahi alo bhi blo).lo :=
  fpMulResultValue_lo_graph ahi alo bhi blo

theorem fpMulSourceBodyResultEnv_hi (yst : EvmState)
    (ahi alo bhi blo : U256) :
    (VEnv.get (fpMulSourceBodyResultEnv ahi alo bhi blo) "\x0075").getD 0 =
      (fpMulResult yst ahi alo bhi blo).1 := by
  rw [fpMulSourceBodyResultEnv_eq]
  calc
    _ = (fpReduceProductValue (fullMulValue ahi alo bhi blo)).hi :=
      fpMulReturnEnvWith_hi ahi alo bhi blo _ _
    _ = (fpMulResultGraph ahi alo bhi blo).hi :=
      congrArg FpMulWideValue.hi (fpMulResultGraph_spec ahi alo bhi blo).symm
    _ = _ := (fpMulResult_hi_graph yst ahi alo bhi blo).symm

theorem fpMulSourceBodyResultEnv_lo (yst : EvmState)
    (ahi alo bhi blo : U256) :
    (VEnv.get (fpMulSourceBodyResultEnv ahi alo bhi blo) "\x0076").getD 0 =
      (fpMulResult yst ahi alo bhi blo).2 := by
  rw [fpMulSourceBodyResultEnv_eq]
  calc
    _ = (fpReduceProductValue (fullMulValue ahi alo bhi blo)).lo :=
      fpMulReturnEnvWith_lo ahi alo bhi blo _ _
    _ = (fpMulResultGraph ahi alo bhi blo).lo :=
      congrArg FpMulWideValue.lo (fpMulResultGraph_spec ahi alo bhi blo).symm
    _ = _ := (fpMulResult_lo_graph yst ahi alo bhi blo).symm

private theorem eval_fpMul_args (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 67 fpMulFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      [.var "ahi", .var "alo", .var "bhi", .var "blo"] =
    .ok (.vals [ahi, alo, bhi, blo] yst) := by
  rfl

/-- The normalized parsed `fpMul` wrapper executes under the closed EVM
semantics and returns the opaque result related to the shared field model. -/
theorem eval_fpMul (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.YulProof.ClosedEvm.exec 68
      [hoist Challenge.YulProof.ClosedEvm.exec.toDialect
        Compilation.referenceCompiledBlock]
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x009" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [(fpMulResult yst ahi alo bhi blo).1,
      (fpMulResult yst ahi alo bhi blo).2]
      (fpMulFinalState yst ahi alo bhi blo)) := by
  have h := Interp.evalExpr_call_normal
    (eval_fpMul_args ahi alo bhi blo yst)
    (show lookupFun fpMulFuns "\x009" = some
      ({ params := ["\x0071", "\x0072", "\x0073", "\x0074"]
         rets := ["\x0075", "\x0076"]
         body := fpMulBody }, fpMulFuns) by rfl)
    (by rfl) (exec_fpMulBody ahi alo bhi blo yst)
  change Interp.evalExpr Challenge.YulProof.ClosedEvm.exec 68
      [hoist Challenge.YulProof.ClosedEvm.exec.toDialect
        Compilation.referenceCompiledBlock]
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x009" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals
      [(VEnv.get (fpMulSourceBodyResultEnv ahi alo bhi blo) "\x0075").getD 0,
        (VEnv.get (fpMulSourceBodyResultEnv ahi alo bhi blo) "\x0076").getD 0]
      yst) at h
  rw [fpMulSourceBodyResultEnv_hi, fpMulSourceBodyResultEnv_lo] at h
  exact h

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
