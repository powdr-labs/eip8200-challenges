import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveStoresExec

set_option warningAsError true

/-! # Twist-constant addition in frozen G2ADD `onCurve` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem soundExpr {n funs V st expr result}
    (h : Interp.evalExpr Challenge.EvmProof.modexpExec n funs
      V st expr = .ok result) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st expr result :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).1
    _ _ _ _ _ h

private theorem onCurveStmt7_shape : onCurveStmt7 =
    .exprStmt (.call "\x0014"
      [.lit (.number 2304), .lit (.number 2304), .lit (.number 2432)]) := by
  rfl

private theorem step_onCurveAdd (yst : EvmState) (x y : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv x y) (onCurveStateAfterConstant yst x y)
      (.call "\x0014"
        [.lit (.number 2304), .lit (.number 2304), .lit (.number 2432)])
      (.vals [] (onCurveStateAfterAdd yst x y)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 71 onCurveBodyFuns
          (onCurveInitialEnv x y) (onCurveStateAfterConstant yst x y)
          [.lit (.number 2304), .lit (.number 2304), .lit (.number 2432)] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 71 fp2AddFuns
          [("out", BitVec.ofNat 256 2304),
            ("a", BitVec.ofNat 256 2304),
            ("b", BitVec.ofNat 256 2432)]
          (onCurveStateAfterConstant yst x y)
          [.var "out", .var "a", .var "b"] := by
    rfl
  have h :
      Interp.evalExpr Challenge.EvmProof.modexpExec 72 onCurveBodyFuns
          (onCurveInitialEnv x y) (onCurveStateAfterConstant yst x y)
          (.call "\x0014"
            [.lit (.number 2304), .lit (.number 2304), .lit (.number 2432)]) =
        .ok (.vals [] (onCurveStateAfterAdd yst x y)) := by
    rw [Interp.evalExpr_call_of_evalArgs_lookup_eq
      (fn := "\x0014") hargs (by rfl)]
    simpa [onCurveStateAfterAdd] using
      eval_fp2AddContractState (onCurveStateAfterConstant yst x y)
        (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2304)
        (BitVec.ofNat 256 2432)
  exact soundExpr h

theorem exec_onCurveStmt7 (yst : EvmState) (x y : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv x y) (onCurveStateAfterConstant yst x y)
      onCurveStmt7 (onCurveInitialEnv x y)
      (onCurveStateAfterAdd yst x y) .normal := by
  rw [onCurveStmt7_shape]
  exact Step.exprStmt (step_onCurveAdd yst x y)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
