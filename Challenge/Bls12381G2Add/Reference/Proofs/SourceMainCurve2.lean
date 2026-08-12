import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainCurve1

set_option warningAsError true

/-! # Second frozen G2ADD on-curve validation branch -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private def curve2Call : Expr Op :=
  .call "\x0018" [.lit (.number 256), .lit (.number 384)]

private def curve2Condition : Expr Op :=
  .builtin .and
    [.builtin .iszero [.var "\x00132"],
      .builtin .iszero [curve2Call]]

private theorem mainPointStmt3_shape : mainPointStmt3 =
    .cond curve2Condition [.exprStmt (.builtin .invalid [])] := by rfl

theorem step_mainCurve2Call (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterCurve1 yst) curve2Call
      (.vals [mainCurve2Result yst] (mainValidatedState yst)) := by
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterCurve1 yst)
      [.lit (.number 256), .lit (.number 384)]
      (.vals [256, 384] (mainAfterCurve1 yst)) :=
    Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit
  have hcall := Step.callOk hargs
    (show lookupFun mainFuns "\x0018" = some (onCurveDecl, mainFuns) by rfl)
    (by rfl) (step_onCurveBody (mainAfterCurve1 yst) 256 384)
    (Or.inl rfl)
  change EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterCurve1 yst) curve2Call
      (.vals
        [(VEnv.get (onCurveBodyResultEnv (mainAfterCurve1 yst) 256 384)
          "\x00121").getD 0]
        (mainValidatedState yst)) at hcall
  rw [onCurveBodyResultEnv_yes] at hcall
  exact hcall

theorem step_mainCurve2Condition (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterCurve1 yst) curve2Condition
      (.vals [mainCurve2ConditionValue yst] (mainValidatedState yst)) := by
  have hcallZero : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterCurve1 yst)
      (.builtin .iszero [curve2Call])
      (.vals [b2w (mainCurve2Result yst = 0)] (mainValidatedState yst)) :=
    Step.builtinOk (Step.argsCons Step.argsNil (step_mainCurve2Call yst)) rfl
  have hinf : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) (.var "\x00132")
      (.vals [mainInf2 yst] (mainValidatedState yst)) := Step.var (by rfl)
  have hinfZero : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst)
      (.builtin .iszero [.var "\x00132"])
      (.vals [b2w (mainInf2 yst = 0)] (mainValidatedState yst)) :=
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

theorem step_mainCurve2_success (yst : EvmState)
    (hvalid : mainCurve2ConditionValue yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterCurve1 yst) mainPointStmt3
      (mainPointEnv yst) (mainValidatedState yst) .normal := by
  rw [mainPointStmt3_shape]
  exact Step.ifFalse (step_mainCurve2Condition yst) hvalid

theorem step_mainCurve2_reject (yst : EvmState)
    (hinvalid : mainCurve2ConditionValue yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterCurve1 yst) mainPointStmt3
      (mainPointEnv yst) (mainInvalidState (mainValidatedState yst)) .halt := by
  rw [mainPointStmt3_shape]
  exact Step.ifTrue (step_mainCurve2Condition yst) hinvalid
    (step_invalidBlock _ _)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
