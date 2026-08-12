import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveAddExec

set_option warningAsError true

/-! # Final equality in frozen G2ADD `onCurve` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem soundExpr {n funs V st e result}
    (h : Interp.evalExpr Challenge.EvmProof.modexpExec n funs V st e =
      .ok result) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st e result :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).1
    _ _ _ _ _ h

private theorem onCurveStmt8_shape : onCurveStmt8 =
    .assign ["\x00121"] (.call "\x0013"
      [.lit (.number 2048), .lit (.number 2304)]) := by
  rfl

def onCurveReturnEnv (yst : EvmState) (x y : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (onCurveInitialEnv x y) ["\x00121"]
    [onCurveResult yst x y]

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
          [.var "a", .var "b"] := by
    rfl
  have hlookup : lookupFun onCurveBodyFuns "\x0013" =
      lookupFun fp2Funs "\x0013" := by
    rfl
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x0013") hargs hlookup]
  rw [eval_fp2Eq]
  rfl

theorem exec_onCurveStmt8 (yst : EvmState) (x y : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv x y) (onCurveStateAfterAdd yst x y)
      onCurveStmt8 (onCurveReturnEnv yst x y)
      (onCurveFinalState yst x y) .normal := by
  rw [onCurveStmt8_shape, onCurveReturnEnv]
  exact Step.assignVal (soundExpr (eval_onCurveEq yst x y)) (by rfl)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
