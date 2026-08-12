import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveEqExec

set_option warningAsError true

/-! # Complete frozen G2ADD `onCurve` execution -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem appendNormal {funs V st pre Vmid stmid suffix Vend stend outcome}
    (hp : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs
      V st pre Vmid stmid .normal)
    (hs : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs
      Vmid stmid suffix Vend stend outcome) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs
      V st (pre ++ suffix) Vend stend outcome := by
  induction pre generalizing V st Vmid stmid with
  | nil => cases hp; simpa using hs
  | cons head rest ih =>
    cases hp with
    | seqCons hh ht => simpa using Step.seqCons hh (ih ht hs)
    | seqStop _ hn => exact (hn rfl).elim

def onCurveBodyResultEnv (yst : EvmState) (x y : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (onCurveInitialEnv x y) (onCurveReturnEnv yst x y)

theorem step_onCurveBodyStmts (yst : EvmState) (x y : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv x y) yst onCurveBody
      (onCurveReturnEnv yst x y) (onCurveFinalState yst x y) .normal := by
  have htail :
      ExecStmts Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
        (onCurveInitialEnv x y) (onCurveStateAfterConstant yst x y)
        [onCurveStmt7, onCurveStmt8]
        (onCurveReturnEnv yst x y) (onCurveFinalState yst x y) .normal :=
    Step.seqCons (exec_onCurveStmt7 yst x y)
      (Step.seqCons (exec_onCurveStmt8 yst x y) Step.seqNil)
  have hfinish := appendNormal (exec_onCurveConstantStores yst x y) htail
  rw [onCurveBody_eq]
  exact Step.seqCons (exec_onCurveStmt0 yst x y)
    (Step.seqCons (exec_onCurveStmt1 yst x y)
      (Step.seqCons (exec_onCurveStmt2 yst x y) hfinish))

theorem step_onCurveBody (yst : EvmState) (x y : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveFuns
      (onCurveInitialEnv x y) yst (.block onCurveBody)
      (onCurveBodyResultEnv yst x y) (onCurveFinalState yst x y)
      .normal := by
  rw [onCurveBodyResultEnv]
  apply Step.block
  rw [onCurveBodyFuns_eq]
  exact step_onCurveBodyStmts yst x y

theorem onCurveBodyResultEnv_yes (yst : EvmState) (x y : U256) :
    (VEnv.get (onCurveBodyResultEnv yst x y) "\x00121").getD 0 =
      onCurveResult yst x y := by
  rfl

theorem step_onCurve (x y : U256) (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveFuns
      [("x", x), ("y", y)] yst
      (.call "\x0018" [.var "x", .var "y"])
      (.vals [onCurveResult yst x y] (onCurveFinalState yst x y)) := by
  have hargsEval :
      Interp.evalArgs Challenge.EvmProof.modexpExec 8 onCurveFuns
        [("x", x), ("y", y)] yst [.var "x", .var "y"] =
      .ok (.vals [x, y] yst) := by
    rfl
  have hargs := (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) 8).2.1
    _ _ _ _ _ hargsEval
  have hcall := Step.callOk hargs lookup_onCurve (by rfl)
    (step_onCurveBody yst x y) (Or.inl rfl)
  change EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveFuns
      [("x", x), ("y", y)] yst
      (.call "\x0018" [.var "x", .var "y"])
      (.vals
        [(VEnv.get (onCurveBodyResultEnv yst x y) "\x00121").getD 0]
        (onCurveFinalState yst x y)) at hcall
  rw [onCurveBodyResultEnv_yes] at hcall
  exact hcall

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
