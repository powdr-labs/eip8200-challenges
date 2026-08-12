import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainCurve2

set_option warningAsError true

/-! # Frozen G2ADD both-infinity return branch -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainBothInfinityValue (yst : EvmState) : U256 :=
  mainInf1 yst &&& mainInf2 yst

def mainBothInfinityClearedState (yst : EvmState) : EvmState :=
  clearPointState (mainValidatedState yst)

def mainBothInfinityReturnState (yst : EvmState) : EvmState :=
  { touchMemory (mainBothInfinityClearedState yst) 0 256 with
    halted := some (.ret,
      readBytes (mainBothInfinityClearedState yst).memory 0 256) }

private theorem mainPointStmt4_shape : mainPointStmt4 =
    .cond (.builtin .and [.var "\x00131", .var "\x00132"])
      [.exprStmt (.call "\x0022" []),
        .exprStmt (.builtin .ret
          [.lit (.number 0), .lit (.number 256)])] := by rfl

private theorem sound_evalExpr {n funs V st expr result}
    (h : Interp.evalExpr Challenge.EvmProof.modexpExec n funs V st expr =
      .ok result) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st expr result :=
  (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).1
    _ _ _ _ _ h

private theorem eval_mainClearPoint (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 ([] :: mainFuns)
      (mainPointEnv yst) (mainValidatedState yst)
      (.call "\x0022" []) =
    .ok (.vals [] (mainBothInfinityClearedState yst)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 ([] :: mainFuns)
          (mainPointEnv yst) (mainValidatedState yst) [] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2Funs []
          (mainValidatedState yst) [] := by rfl
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x0022") hargs (by rfl)]
  exact eval_clearPoint _

theorem step_mainBothInfinityCondition (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst)
      (.builtin .and [.var "\x00131", .var "\x00132"])
      (.vals [mainBothInfinityValue yst] (mainValidatedState yst)) := by
  have hinf1 : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) (.var "\x00131")
      (.vals [mainInf1 yst] (mainValidatedState yst)) := Step.var (by rfl)
  have hinf2 : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) (.var "\x00132")
      (.vals [mainInf2 yst] (mainValidatedState yst)) := Step.var (by rfl)
  exact Step.builtinOk
    (Step.argsCons (Step.argsCons Step.argsNil hinf2) hinf1) rfl

theorem step_mainBothInfinity_return (yst : EvmState)
    (hboth : mainBothInfinityValue yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) mainPointStmt4
      (mainPointEnv yst) (mainBothInfinityReturnState yst) .halt := by
  rw [mainPointStmt4_shape]
  have hclear : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainValidatedState yst)
      (.call "\x0022" [])
      (.vals [] (mainBothInfinityClearedState yst)) :=
    sound_evalExpr (eval_mainClearPoint yst)
  have hzero : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainBothInfinityClearedState yst)
      (.lit (.number 0)) (.vals [0] (mainBothInfinityClearedState yst)) :=
    Step.lit
  have hsize : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainBothInfinityClearedState yst)
      (.lit (.number 256)) (.vals [256] (mainBothInfinityClearedState yst)) :=
    Step.lit
  have hret : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainBothInfinityClearedState yst)
      (.builtin .ret [.lit (.number 0), .lit (.number 256)])
      (.halt (mainBothInfinityReturnState yst)) :=
    Step.builtinHalt
      (Step.argsCons (Step.argsCons Step.argsNil hsize) hzero) rfl
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainValidatedState yst)
      [.exprStmt (.call "\x0022" []),
        .exprStmt (.builtin .ret
          [.lit (.number 0), .lit (.number 256)])]
      (mainPointEnv yst) (mainBothInfinityReturnState yst) .halt :=
    Step.seqCons (Step.exprStmt hclear)
      (Step.seqStop (Step.exprStmtHalt hret) (by decide))
  have hseq' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect
        [.exprStmt (.call "\x0022" []),
          .exprStmt (.builtin .ret
            [.lit (.number 0), .lit (.number 256)])] :: mainFuns)
      (mainPointEnv yst) (mainValidatedState yst)
      [.exprStmt (.call "\x0022" []),
        .exprStmt (.builtin .ret
          [.lit (.number 0), .lit (.number 256)])]
      (mainPointEnv yst) (mainBothInfinityReturnState yst) .halt := by
    simpa [hoist] using hseq
  have hblock := Step.block
    (D := Challenge.EvmProof.modexpExec.toDialect) hseq'
  exact Step.ifTrue (step_mainBothInfinityCondition yst) hboth
    (by simpa [restore] using hblock)

theorem step_mainBothInfinity_continue (yst : EvmState)
    (hboth : mainBothInfinityValue yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) mainPointStmt4
      (mainPointEnv yst) (mainValidatedState yst) .normal := by
  rw [mainPointStmt4_shape]
  exact Step.ifFalse (step_mainBothInfinityCondition yst) hboth

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
