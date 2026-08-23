import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainPointExec
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulMemory
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! # Frozen G1ADD curve-validation prefix execution -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem sound_evalArgs {n funs V st args vals st'}
    (h : Interp.evalArgs Challenge.EvmProof.modexpExec n funs V st args =
      .ok (.vals vals st')) :
    EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V st args
      (.vals vals st') :=
  (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hbuiltin =>
      Challenge.EvmProof.modexpBuiltinFn_sound hbuiltin) n).2.1
    _ _ _ _ _ h

private theorem eval_curve1Args (yst : EvmState) :
    Interp.evalArgs Challenge.EvmProof.modexpExec 8 mainFuns
      (mainPointEnv yst) (mainAfterInf2Reads yst)
      [.builtin .mload [.lit (.number 0)],
        .builtin .mload [.lit (.number 32)],
        .builtin .mload [.lit (.number 64)],
        .builtin .mload [.lit (.number 96)]] =
      .ok (.vals
        [mainDecodedWord yst 0, mainDecodedWord yst 32,
          mainDecodedWord yst 64, mainDecodedWord yst 96]
        (mainCurve1ArgsState yst)) := by
  simp [Interp.evalArgs, Interp.evalExpr,
    mainCurve1ArgsState, afterFourLoads,
    mainDecodedWord, mainAfterInf2Reads, mainAfterInf1Reads,
    mainAfterCanonicalReads, mainAfterPaddingReads,
    Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
    stepOp, EVM.litValue]

theorem step_curve1Call (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterInf2Reads yst)
      (.call "\x0011"
        [.builtin .mload [.lit (.number 0)],
          .builtin .mload [.lit (.number 32)],
          .builtin .mload [.lit (.number 64)],
          .builtin .mload [.lit (.number 96)]])
      (.vals [mainCurve1Result yst] (mainAfterCurve1 yst)) := by
  have hargs := sound_evalArgs (eval_curve1Args yst)
  have hcall := Step.callOk hargs lookup_onCurve (by rfl)
    (step_onCurveBody
      (mainDecodedWord yst 0) (mainDecodedWord yst 32)
      (mainDecodedWord yst 64) (mainDecodedWord yst 96)
      (mainCurve1ArgsState yst)) (Or.inl rfl)
  change EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterInf2Reads yst)
      (.call "\x0011"
        [.builtin .mload [.lit (.number 0)],
          .builtin .mload [.lit (.number 32)],
          .builtin .mload [.lit (.number 64)],
          .builtin .mload [.lit (.number 96)]])
      (.vals
        [(VEnv.get (onCurveBodyResultEnv (mainCurve1ArgsState yst)
          (mainDecodedWord yst 0) (mainDecodedWord yst 32)
          (mainDecodedWord yst 64) (mainDecodedWord yst 96))
          "\x0085").getD 0]
        (mainAfterCurve1 yst)) at hcall
  rw [onCurveBodyResultEnv_yes] at hcall
  exact hcall

private def curve1Call : Expr Op :=
  .call "\x0011"
    [.builtin .mload [.lit (.number 0)],
      .builtin .mload [.lit (.number 32)],
      .builtin .mload [.lit (.number 64)],
      .builtin .mload [.lit (.number 96)]]

private def curve1Condition : Expr Op :=
  .builtin .and
    [.builtin .iszero [.var "\x0096"],
      .builtin .iszero [curve1Call]]

private theorem mainCurve1Stmt_shape : mainCurve1Stmt =
    .cond curve1Condition [.exprStmt (.builtin .invalid [])] := by rfl

theorem step_curve1Condition (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterInf2Reads yst) curve1Condition
      (.vals [mainCurve1ConditionValue yst] (mainAfterCurve1 yst)) := by
  have hcall : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterInf2Reads yst) curve1Call
      (.vals [mainCurve1Result yst] (mainAfterCurve1 yst)) := by
    exact step_curve1Call yst
  have hcallZero : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterInf2Reads yst)
      (.builtin .iszero [curve1Call])
      (.vals [b2w (mainCurve1Result yst = 0)] (mainAfterCurve1 yst)) := by
    exact Step.builtinOk (D := Challenge.EvmProof.modexpExec.toDialect)
      (Step.argsCons Step.argsNil hcall) rfl
  have hinf : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterCurve1 yst) (.var "\x0096")
      (.vals [mainInf1 yst] (mainAfterCurve1 yst)) := Step.var (by rfl)
  have hinfZero : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterCurve1 yst)
      (.builtin .iszero [.var "\x0096"])
      (.vals [b2w (mainInf1 yst = 0)] (mainAfterCurve1 yst)) := by
    exact Step.builtinOk (D := Challenge.EvmProof.modexpExec.toDialect)
      (Step.argsCons Step.argsNil hinf) rfl
  exact Step.builtinOk (D := Challenge.EvmProof.modexpExec.toDialect)
    (Step.argsCons (Step.argsCons Step.argsNil hcallZero) hinfZero) rfl

private theorem step_invalidBlock
    (V : VEnv Challenge.EvmProof.modexpExec.toDialect) (yst : EvmState) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns V yst
      (.block [.exprStmt (.builtin .invalid [])]) V
      (mainInvalidState yst) .halt := by
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) V yst [.exprStmt (.builtin .invalid [])]
      V (mainInvalidState yst) .halt := by
    apply Step.seqStop
    · apply Step.exprStmtHalt
      exact Step.builtinHalt (D := Challenge.EvmProof.modexpExec.toDialect)
        Step.argsNil rfl
    · decide
  have hseq' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect
        [.exprStmt (.builtin .invalid [])] :: mainFuns)
      V yst [.exprStmt (.builtin .invalid [])]
      V (mainInvalidState yst) .halt := by
    simpa [hoist] using hseq
  have hblock := Step.block (D := Challenge.EvmProof.modexpExec.toDialect) hseq'
  simpa [restore] using hblock

theorem step_mainCurve1_success (yst : EvmState)
    (hvalid : mainCurve1ConditionValue yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterInf2Reads yst) mainCurve1Stmt
      (mainPointEnv yst) (mainAfterCurve1 yst) .normal := by
  rw [mainCurve1Stmt_shape]
  exact Step.ifFalse (step_curve1Condition yst) hvalid

theorem step_mainCurve1_reject (yst : EvmState)
    (hinvalid : mainCurve1ConditionValue yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterInf2Reads yst) mainCurve1Stmt
      (mainPointEnv yst) (mainInvalidState (mainAfterCurve1 yst)) .halt := by
  rw [mainCurve1Stmt_shape]
  exact Step.ifTrue (step_curve1Condition yst) hinvalid
    (step_invalidBlock _ _)

private theorem eval_curve2Args (yst : EvmState) :
    Interp.evalArgs Challenge.EvmProof.modexpExec 8 mainFuns
      (mainPointEnv yst) (mainAfterCurve1 yst)
      [.builtin .mload [.lit (.number 128)],
        .builtin .mload [.lit (.number 160)],
        .builtin .mload [.lit (.number 192)],
        .builtin .mload [.lit (.number 224)]] =
      .ok (.vals
        [mainDecodedWord yst 128, mainDecodedWord yst 160,
          mainDecodedWord yst 192, mainDecodedWord yst 224]
        (mainCurve2ArgsState yst)) := by
  have hpreserve (offset : Nat) (hoffset : offset + 32 ≤ 1024) :
      loadWord (mainAfterCurve1 yst).memory offset =
        mainDecodedWord yst offset := by
    rw [show mainAfterCurve1 yst =
      onCurveFinalState (mainCurve1ArgsState yst)
        (mainDecodedWord yst 0) (mainDecodedWord yst 32)
        (mainDecodedWord yst 64) (mainDecodedWord yst 96) by rfl]
    unfold onCurveFinalState onCurveState2 onCurveState1
    rw [fpMulFinalState_loadWord_before_scratch _ _ _ _ _ _ hoffset]
    rw [fpMulFinalState_loadWord_before_scratch _ _ _ _ _ _ hoffset]
    rw [fpMulFinalState_loadWord_before_scratch _ _ _ _ _ _ hoffset]
    simp [mainCurve1ArgsState, afterFourLoads, mainDecodedWord,
      mainAfterInf2Reads, mainAfterInf1Reads,
      mainAfterCanonicalReads, mainAfterPaddingReads]
  simp [Interp.evalArgs, Interp.evalExpr,
    mainCurve2ArgsState, afterFourLoads, mainDecodedWord,
    Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
    stepOp, EVM.litValue, hpreserve]

private def curve2Call : Expr Op :=
  .call "\x0011"
    [.builtin .mload [.lit (.number 128)],
      .builtin .mload [.lit (.number 160)],
      .builtin .mload [.lit (.number 192)],
      .builtin .mload [.lit (.number 224)]]

theorem step_curve2Call (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterCurve1 yst) curve2Call
      (.vals [mainCurve2Result yst] (mainValidatedState yst)) := by
  have hargs := sound_evalArgs (eval_curve2Args yst)
  have hcall := Step.callOk hargs lookup_onCurve (by rfl)
    (step_onCurveBody
      (mainDecodedWord yst 128) (mainDecodedWord yst 160)
      (mainDecodedWord yst 192) (mainDecodedWord yst 224)
      (mainCurve2ArgsState yst)) (Or.inl rfl)
  change EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterCurve1 yst) curve2Call
      (.vals
        [(VEnv.get (onCurveBodyResultEnv (mainCurve2ArgsState yst)
          (mainDecodedWord yst 128) (mainDecodedWord yst 160)
          (mainDecodedWord yst 192) (mainDecodedWord yst 224))
          "\x0085").getD 0]
        (mainValidatedState yst)) at hcall
  rw [onCurveBodyResultEnv_yes] at hcall
  exact hcall

private def curve2Condition : Expr Op :=
  .builtin .and
    [.builtin .iszero [.var "\x0097"],
      .builtin .iszero [curve2Call]]

private theorem mainCurve2Stmt_shape : mainCurve2Stmt =
    .cond curve2Condition [.exprStmt (.builtin .invalid [])] := by rfl

theorem step_curve2Condition (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterCurve1 yst) curve2Condition
      (.vals [mainCurve2ConditionValue yst] (mainValidatedState yst)) := by
  have hcall := step_curve2Call yst
  have hcallZero : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterCurve1 yst)
      (.builtin .iszero [curve2Call])
      (.vals [b2w (mainCurve2Result yst = 0)] (mainValidatedState yst)) := by
    exact Step.builtinOk (D := Challenge.EvmProof.modexpExec.toDialect)
      (Step.argsCons Step.argsNil hcall) rfl
  have hinf : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) (.var "\x0097")
      (.vals [mainInf2 yst] (mainValidatedState yst)) := Step.var (by rfl)
  have hinfZero : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst)
      (.builtin .iszero [.var "\x0097"])
      (.vals [b2w (mainInf2 yst = 0)] (mainValidatedState yst)) := by
    exact Step.builtinOk (D := Challenge.EvmProof.modexpExec.toDialect)
      (Step.argsCons Step.argsNil hinf) rfl
  exact Step.builtinOk (D := Challenge.EvmProof.modexpExec.toDialect)
    (Step.argsCons (Step.argsCons Step.argsNil hcallZero) hinfZero) rfl

theorem step_mainCurve2_success (yst : EvmState)
    (hvalid : mainCurve2ConditionValue yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterCurve1 yst) mainCurve2Stmt
      (mainPointEnv yst) (mainValidatedState yst) .normal := by
  rw [mainCurve2Stmt_shape]
  exact Step.ifFalse (step_curve2Condition yst) hvalid

theorem step_mainCurve2_reject (yst : EvmState)
    (hinvalid : mainCurve2ConditionValue yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainAfterCurve1 yst) mainCurve2Stmt
      (mainPointEnv yst) (mainInvalidState (mainValidatedState yst)) .halt := by
  rw [mainCurve2Stmt_shape]
  exact Step.ifTrue (step_curve2Condition yst) hinvalid
    (step_invalidBlock _ _)

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
