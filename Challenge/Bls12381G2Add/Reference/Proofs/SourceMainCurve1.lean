import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainPointExec

set_option warningAsError true

/-! # First frozen G2ADD on-curve validation branch -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private def curve1Call : Expr Op :=
  .call "\x0018" [.lit (.number 0), .lit (.number 128)]

private def curve1Condition : Expr Op :=
  .builtin .and
    [.builtin .iszero [.var "\x00131"],
      .builtin .iszero [curve1Call]]

private theorem mainPointStmt2_shape : mainPointStmt2 =
    .cond curve1Condition [.exprStmt (.builtin .invalid [])] := by rfl

theorem step_mainCurve1Call (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterInf2Reads yst) curve1Call
      (.vals [mainCurve1Result yst] (mainAfterCurve1 yst)) := by
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterInf2Reads yst)
      [.lit (.number 0), .lit (.number 128)]
      (.vals [0, 128] (mainAfterInf2Reads yst)) :=
    Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit
  have hcall := Step.callOk hargs
    (show lookupFun mainFuns "\x0018" = some (onCurveDecl, mainFuns) by rfl)
    (by rfl) (step_onCurveBody (mainAfterInf2Reads yst) 0 128)
    (Or.inl rfl)
  change EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterInf2Reads yst) curve1Call
      (.vals
        [(VEnv.get (onCurveBodyResultEnv (mainAfterInf2Reads yst) 0 128)
          "\x00121").getD 0]
        (mainAfterCurve1 yst)) at hcall
  rw [onCurveBodyResultEnv_yes] at hcall
  exact hcall

theorem step_mainCurve1Condition (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterInf2Reads yst) curve1Condition
      (.vals [mainCurve1ConditionValue yst] (mainAfterCurve1 yst)) := by
  have hcallZero : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterInf2Reads yst)
      (.builtin .iszero [curve1Call])
      (.vals [b2w (mainCurve1Result yst = 0)] (mainAfterCurve1 yst)) :=
    Step.builtinOk (Step.argsCons Step.argsNil (step_mainCurve1Call yst)) rfl
  have hinf : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterCurve1 yst) (.var "\x00131")
      (.vals [mainInf1 yst] (mainAfterCurve1 yst)) := Step.var (by rfl)
  have hinfZero : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterCurve1 yst)
      (.builtin .iszero [.var "\x00131"])
      (.vals [b2w (mainInf1 yst = 0)] (mainAfterCurve1 yst)) :=
    Step.builtinOk (Step.argsCons Step.argsNil hinf) rfl
  exact Step.builtinOk
    (Step.argsCons (Step.argsCons Step.argsNil hcallZero) hinfZero) rfl

private theorem step_invalidBlock
    (V : VEnv Challenge.EvmProof.modexpExec.toDialect) (yst : EvmState) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns V yst
      (.block [.exprStmt (.builtin .invalid [])]) V
      (mainInvalidState yst) .halt := by
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) V yst [.exprStmt (.builtin .invalid [])]
      V (mainInvalidState yst) .halt :=
    Step.seqStop (Step.exprStmtHalt
      (Step.builtinHalt Step.argsNil rfl)) (by decide)
  have hseq' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect
        [.exprStmt (.builtin .invalid [])] :: mainFuns)
      V yst [.exprStmt (.builtin .invalid [])]
      V (mainInvalidState yst) .halt := by
    simpa [hoist] using hseq
  have hblock := Step.block
    (D := Challenge.EvmProof.modexpExec.toDialect) hseq'
  simpa [restore] using hblock

theorem step_mainCurve1_success (yst : EvmState)
    (hvalid : mainCurve1ConditionValue yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterInf2Reads yst) mainPointStmt2
      (mainPointEnv yst) (mainAfterCurve1 yst) .normal := by
  rw [mainPointStmt2_shape]
  exact Step.ifFalse (step_mainCurve1Condition yst) hvalid

theorem step_mainCurve1_reject (yst : EvmState)
    (hinvalid : mainCurve1ConditionValue yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterInf2Reads yst) mainPointStmt2
      (mainPointEnv yst) (mainInvalidState (mainAfterCurve1 yst)) .halt := by
  rw [mainPointStmt2_shape]
  exact Step.ifTrue (step_mainCurve1Condition yst) hinvalid
    (step_invalidBlock _ _)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
