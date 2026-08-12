import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainBothInfinity

set_option warningAsError true

/-! # Frozen G2ADD first-infinity identity branch -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainFirstInfinityCopyState (yst : EvmState) : EvmState :=
  copyPointState (mainValidatedState yst) 256

def mainFirstInfinityReturnState (yst : EvmState) : EvmState :=
  { touchMemory (mainFirstInfinityCopyState yst) 0 256 with
    halted := some (.ret,
      readBytes (mainFirstInfinityCopyState yst).memory 0 256) }

private theorem mainPointStmt5_shape : mainPointStmt5 =
    .cond (.var "\x00131")
      [.exprStmt (.call "\x0023" [.lit (.number 256)]),
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

private theorem eval_mainCopySecond (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 ([] :: mainFuns)
      (mainPointEnv yst) (mainValidatedState yst)
      (.call "\x0023" [.lit (.number 256)]) =
    .ok (.vals [] (mainFirstInfinityCopyState yst)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 ([] :: mainFuns)
          (mainPointEnv yst) (mainValidatedState yst)
          [.lit (.number 256)] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2Funs
          [("point", (256 : U256))] (mainValidatedState yst)
          [.var "point"] := by rfl
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x0023") hargs (by rfl)]
  exact eval_copyPoint 256 _

theorem step_mainFirstInfinity_return (yst : EvmState)
    (hfirst : mainInf1 yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) mainPointStmt5
      (mainPointEnv yst) (mainFirstInfinityReturnState yst) .halt := by
  rw [mainPointStmt5_shape]
  have hcondition : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) (.var "\x00131")
      (.vals [mainInf1 yst] (mainValidatedState yst)) := Step.var (by rfl)
  have hcopy : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainValidatedState yst)
      (.call "\x0023" [.lit (.number 256)])
      (.vals [] (mainFirstInfinityCopyState yst)) :=
    sound_evalExpr (eval_mainCopySecond yst)
  have hzero : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainFirstInfinityCopyState yst)
      (.lit (.number 0)) (.vals [0] (mainFirstInfinityCopyState yst)) :=
    Step.lit
  have hsize : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainFirstInfinityCopyState yst)
      (.lit (.number 256)) (.vals [256] (mainFirstInfinityCopyState yst)) :=
    Step.lit
  have hret : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainFirstInfinityCopyState yst)
      (.builtin .ret [.lit (.number 0), .lit (.number 256)])
      (.halt (mainFirstInfinityReturnState yst)) :=
    Step.builtinHalt
      (Step.argsCons (Step.argsCons Step.argsNil hsize) hzero) rfl
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainValidatedState yst)
      [.exprStmt (.call "\x0023" [.lit (.number 256)]),
        .exprStmt (.builtin .ret
          [.lit (.number 0), .lit (.number 256)])]
      (mainPointEnv yst) (mainFirstInfinityReturnState yst) .halt :=
    Step.seqCons (Step.exprStmt hcopy)
      (Step.seqStop (Step.exprStmtHalt hret) (by decide))
  have hseq' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect
        [.exprStmt (.call "\x0023" [.lit (.number 256)]),
          .exprStmt (.builtin .ret
            [.lit (.number 0), .lit (.number 256)])] :: mainFuns)
      (mainPointEnv yst) (mainValidatedState yst)
      [.exprStmt (.call "\x0023" [.lit (.number 256)]),
        .exprStmt (.builtin .ret
          [.lit (.number 0), .lit (.number 256)])]
      (mainPointEnv yst) (mainFirstInfinityReturnState yst) .halt := by
    simpa [hoist] using hseq
  have hblock := Step.block
    (D := Challenge.EvmProof.modexpExec.toDialect) hseq'
  exact Step.ifTrue hcondition hfirst (by simpa [restore] using hblock)

theorem step_mainFirstInfinity_continue (yst : EvmState)
    (hfirst : mainInf1 yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) mainPointStmt5
      (mainPointEnv yst) (mainValidatedState yst) .normal := by
  rw [mainPointStmt5_shape]
  exact Step.ifFalse (Step.var (by rfl)) hfirst

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
