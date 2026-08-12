import Challenge.Bls12381G2Msm.Reference.Proofs.SourceOnCurveDefs
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Exact staged execution of frozen G2MSM `onCurve`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem soundArgs {V st args vals}
    (h : Interp.evalArgs Challenge.EvmProof.modexpExec 8 onCurveBodyFuns
      V st args = .ok (.vals vals st)) :
    EvalArgs Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      V st args (.vals vals st) :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) 8).2.1
    _ _ _ _ _ h

private theorem soundStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt Challenge.EvmProof.modexpExec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect funs V st stmt V' st' outcome :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.1
    _ _ _ _ _ _ _ h

private theorem soundStmts {n funs V st stmts V' st' outcome}
    (h : Interp.execStmts Challenge.EvmProof.modexpExec n funs V st stmts =
      .ok (V', st', outcome)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st stmts V' st' outcome :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.2.1
    _ _ _ _ _ _ _ h

private theorem soundExpr {n funs V st e result}
    (h : Interp.evalExpr Challenge.EvmProof.modexpExec n funs V st e =
      .ok result) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st e result :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).1
    _ _ _ _ _ h

private theorem appendNormal {funs V st pre Vmid stmid suffix Vend stend outcome}
    (hp : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st pre
      Vmid stmid .normal)
    (hs : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs Vmid stmid suffix
      Vend stend outcome) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st (pre ++ suffix)
      Vend stend outcome := by
  induction pre generalizing V st Vmid stmid with
  | nil => cases hp; simpa using hs
  | cons head rest ih =>
    cases hp with
    | seqCons hh ht => simpa using Step.seqCons hh (ih ht hs)
    | seqStop _ hn => exact (hn rfl).elim

private theorem lookup_fp2Mul_onCurve : lookupFun onCurveBodyFuns "\x0016" =
    some (fp2MulDecl, fp2MulFuns) := by rfl

private theorem fp2MulFinalState_eq_g2Add (yst : EvmState) (out a b : U256) :
    fp2MulFinalState yst out a b =
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulFinalState
        yst out a b := by rfl

private theorem onCurveStmt0_shape : onCurveStmt0 =
    .exprStmt (.call "\x0016"
      [.lit (.number 2048), .var "\x00126", .var "\x00126"]) := by rfl

theorem exec_onCurveStmt0 (yst : EvmState) (x y : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv x y) yst onCurveStmt0
      (onCurveInitialEnv x y) (onCurveStateAfterY2 yst y) .normal := by
  rw [onCurveStmt0_shape]
  apply Step.exprStmt
  have hargs := soundArgs (V := onCurveInitialEnv x y) (st := yst)
    (args := [.lit (.number 2048), .var "\x00126", .var "\x00126"])
    (vals := [BitVec.ofNat 256 2048, y, y]) (by rfl)
  have hcall := Step.callOk hargs lookup_fp2Mul_onCurve (by rfl)
    (step_fp2MulBody yst (BitVec.ofNat 256 2048) y y) (Or.inl rfl)
  rw [fp2MulFinalState_eq_g2Add] at hcall
  simpa [fp2MulDecl, onCurveStateAfterY2,
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.onCurveStateAfterY2]
    using hcall

private theorem onCurveStmt1_shape : onCurveStmt1 =
    .exprStmt (.call "\x0016"
      [.lit (.number 2176), .var "\x00125", .var "\x00125"]) := by rfl

theorem exec_onCurveStmt1 (yst : EvmState) (x y : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv x y) (onCurveStateAfterY2 yst y) onCurveStmt1
      (onCurveInitialEnv x y) (onCurveStateAfterX2 yst x y) .normal := by
  rw [onCurveStmt1_shape]
  apply Step.exprStmt
  have hargs := soundArgs (V := onCurveInitialEnv x y)
    (st := onCurveStateAfterY2 yst y)
    (args := [.lit (.number 2176), .var "\x00125", .var "\x00125"])
    (vals := [BitVec.ofNat 256 2176, x, x]) (by rfl)
  have hcall := Step.callOk hargs lookup_fp2Mul_onCurve (by rfl)
    (step_fp2MulBody (onCurveStateAfterY2 yst y)
      (BitVec.ofNat 256 2176) x x) (Or.inl rfl)
  rw [fp2MulFinalState_eq_g2Add] at hcall
  simpa [fp2MulDecl, onCurveStateAfterX2,
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.onCurveStateAfterX2]
    using hcall

private theorem onCurveStmt2_shape : onCurveStmt2 =
    .exprStmt (.call "\x0016"
      [.lit (.number 2304), .lit (.number 2176), .var "\x00125"]) := by rfl

theorem exec_onCurveStmt2 (yst : EvmState) (x y : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv x y) (onCurveStateAfterX2 yst x y) onCurveStmt2
      (onCurveInitialEnv x y) (onCurveStateAfterX3 yst x y) .normal := by
  rw [onCurveStmt2_shape]
  apply Step.exprStmt
  have hargs := soundArgs (V := onCurveInitialEnv x y)
    (st := onCurveStateAfterX2 yst x y)
    (args := [.lit (.number 2304), .lit (.number 2176), .var "\x00125"])
    (vals := [BitVec.ofNat 256 2304, BitVec.ofNat 256 2176, x]) (by rfl)
  have hcall := Step.callOk hargs lookup_fp2Mul_onCurve (by rfl)
    (step_fp2MulBody (onCurveStateAfterX2 yst x y)
      (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2176) x) (Or.inl rfl)
  rw [fp2MulFinalState_eq_g2Add] at hcall
  simpa [fp2MulDecl, onCurveStateAfterX3,
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.onCurveStateAfterX3]
    using hcall

theorem exec_onCurveConstantStores (yst : EvmState) (x y : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv x y) (onCurveStateAfterX3 yst x y)
      [onCurveStmt3, onCurveStmt4, onCurveStmt5, onCurveStmt6]
      (onCurveInitialEnv x y) (onCurveStateAfterConstant yst x y)
      .normal := by
  exact soundStmts (n := 16) (by rfl)

private theorem lookup_fp2Add_onCurve : lookupFun onCurveBodyFuns "\x0014" =
    some (fp2AddDecl, fp2AddFuns) := by rfl

private theorem onCurveStmt7_shape : onCurveStmt7 =
    .exprStmt (.call "\x0014"
      [.lit (.number 2304), .lit (.number 2304), .lit (.number 2432)]) := by rfl

theorem exec_onCurveStmt7 (yst : EvmState) (x y : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv x y) (onCurveStateAfterConstant yst x y)
      onCurveStmt7 (onCurveInitialEnv x y)
      (onCurveStateAfterAdd yst x y) .normal := by
  rw [onCurveStmt7_shape]
  apply Step.exprStmt
  have hargs := soundArgs (V := onCurveInitialEnv x y)
    (st := onCurveStateAfterConstant yst x y)
    (args := [.lit (.number 2304), .lit (.number 2304), .lit (.number 2432)])
    (vals := [BitVec.ofNat 256 2304, BitVec.ofNat 256 2304,
      BitVec.ofNat 256 2432]) (by rfl)
  have hbody : ExecStmt Challenge.EvmProof.modexpExec.toDialect fp2AddFuns
      (fp2AddInitialEnv (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2304)
        (BitVec.ofNat 256 2432)) (onCurveStateAfterConstant yst x y)
      (.block fp2AddBody)
      (fp2AddBodyResultEnv (onCurveStateAfterConstant yst x y)
        (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2304)
        (BitVec.ofNat 256 2432))
      (fp2AddFinalState (onCurveStateAfterConstant yst x y)
        (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2304)
        (BitVec.ofNat 256 2432)) .normal :=
    soundStmt (exec_fp2AddBody (onCurveStateAfterConstant yst x y)
      (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2304)
      (BitVec.ofNat 256 2432))
  have hcall := Step.callOk hargs lookup_fp2Add_onCurve (by rfl)
    hbody (Or.inl rfl)
  simpa [fp2AddDecl, onCurveStateAfterAdd,
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.onCurveStateAfterAdd]
    using hcall

def onCurveReturnEnv (yst : EvmState) (x y : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (onCurveInitialEnv x y) ["\x00127"] [onCurveResult yst x y]

private theorem onCurveStmt8_shape : onCurveStmt8 =
    .assign ["\x00127"] (.call "\x0013"
      [.lit (.number 2048), .lit (.number 2304)]) := by rfl

private theorem eval_onCurveEq (yst : EvmState) (x y : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 onCurveBodyFuns
      (onCurveInitialEnv x y) (onCurveStateAfterAdd yst x y)
      (.call "\x0013" [.lit (.number 2048), .lit (.number 2304)]) =
    .ok (.vals [onCurveResult yst x y] (onCurveFinalState yst x y)) := by
  let s := onCurveStateAfterAdd yst x y
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 onCurveBodyFuns
          (onCurveInitialEnv x y) s
          [.lit (.number 2048), .lit (.number 2304)] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2Funs
          [("a", BitVec.ofNat 256 2048), ("b", BitVec.ofNat 256 2304)] s
          [.var "a", .var "b"] := by rfl
  have hlookup : lookupFun onCurveBodyFuns "\x0013" =
      lookupFun fp2Funs "\x0013" := by rfl
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x0013") hargs hlookup, eval_fp2Eq]
  rfl

theorem exec_onCurveStmt8 (yst : EvmState) (x y : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv x y) (onCurveStateAfterAdd yst x y)
      onCurveStmt8 (onCurveReturnEnv yst x y)
      (onCurveFinalState yst x y) .normal := by
  rw [onCurveStmt8_shape, onCurveReturnEnv]
  exact Step.assignVal (soundExpr (eval_onCurveEq yst x y)) (by rfl)

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
    (VEnv.get (onCurveBodyResultEnv yst x y) "\x00127").getD 0 =
      onCurveResult yst x y := by rfl

theorem step_onCurve (x y : U256) (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveFuns
      [("x", x), ("y", y)] yst
      (.call "\x0018" [.var "x", .var "y"])
      (.vals [onCurveResult yst x y] (onCurveFinalState yst x y)) := by
  have hargsEval :
      Interp.evalArgs Challenge.EvmProof.modexpExec 8 onCurveFuns
        [("x", x), ("y", y)] yst [.var "x", .var "y"] =
      .ok (.vals [x, y] yst) := by rfl
  have hargs := (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) 8).2.1
    _ _ _ _ _ hargsEval
  have hcall := Step.callOk hargs lookup_onCurve (by rfl)
    (step_onCurveBody yst x y) (Or.inl rfl)
  change EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveFuns
      [("x", x), ("y", y)] yst
      (.call "\x0018" [.var "x", .var "y"])
      (.vals [(VEnv.get (onCurveBodyResultEnv yst x y) "\x00127").getD 0]
        (onCurveFinalState yst x y)) at hcall
  rw [onCurveBodyResultEnv_yes] at hcall
  exact hcall

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
