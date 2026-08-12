import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveDefs

set_option warningAsError true

/-! # Multiplication calls in frozen G2ADD `onCurve` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem soundArgs {V st args vals}
    (h : Interp.evalArgs Challenge.EvmProof.modexpExec 8 onCurveBodyFuns
      V st args = .ok (.vals vals st)) :
    EvalArgs Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      V st args (.vals vals st) :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) 8).2.1
    _ _ _ _ _ h

private theorem lookup_fp2Mul_onCurve : lookupFun onCurveBodyFuns "\x0016" =
    some (fp2MulDecl, fp2MulFuns) := by rfl

private theorem onCurveStmt0_shape : onCurveStmt0 =
    .exprStmt (.call "\x0016"
      [.lit (.number 2048), .var "\x00120", .var "\x00120"]) := by rfl

private theorem step_onCurveMul0 (yst : EvmState) (x y : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv x y) yst
      (.call "\x0016"
        [.lit (.number 2048), .var "\x00120", .var "\x00120"])
      (.vals [] (onCurveStateAfterY2 yst y)) := by
  have hargs := soundArgs (V := onCurveInitialEnv x y) (st := yst)
    (args := [.lit (.number 2048), .var "\x00120", .var "\x00120"])
    (vals := [BitVec.ofNat 256 2048, y, y]) (by rfl)
  have hcall := Step.callOk hargs lookup_fp2Mul_onCurve (by rfl)
    (step_fp2MulBody yst (BitVec.ofNat 256 2048) y y) (Or.inl rfl)
  simpa [fp2MulDecl, onCurveStateAfterY2] using hcall

theorem exec_onCurveStmt0 (yst : EvmState) (x y : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv x y) yst onCurveStmt0
      (onCurveInitialEnv x y) (onCurveStateAfterY2 yst y) .normal := by
  rw [onCurveStmt0_shape]
  exact Step.exprStmt (step_onCurveMul0 yst x y)

private theorem onCurveStmt1_shape : onCurveStmt1 =
    .exprStmt (.call "\x0016"
      [.lit (.number 2176), .var "\x00119", .var "\x00119"]) := by rfl

private theorem step_onCurveMul1 (yst : EvmState) (x y : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv x y) (onCurveStateAfterY2 yst y)
      (.call "\x0016"
        [.lit (.number 2176), .var "\x00119", .var "\x00119"])
      (.vals [] (onCurveStateAfterX2 yst x y)) := by
  have hargs := soundArgs (V := onCurveInitialEnv x y)
    (st := onCurveStateAfterY2 yst y)
    (args := [.lit (.number 2176), .var "\x00119", .var "\x00119"])
    (vals := [BitVec.ofNat 256 2176, x, x]) (by rfl)
  have hcall := Step.callOk hargs lookup_fp2Mul_onCurve (by rfl)
    (step_fp2MulBody (onCurveStateAfterY2 yst y)
      (BitVec.ofNat 256 2176) x x) (Or.inl rfl)
  simpa [fp2MulDecl, onCurveStateAfterX2] using hcall

theorem exec_onCurveStmt1 (yst : EvmState) (x y : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv x y) (onCurveStateAfterY2 yst y) onCurveStmt1
      (onCurveInitialEnv x y) (onCurveStateAfterX2 yst x y) .normal := by
  rw [onCurveStmt1_shape]
  exact Step.exprStmt (step_onCurveMul1 yst x y)

private theorem onCurveStmt2_shape : onCurveStmt2 =
    .exprStmt (.call "\x0016"
      [.lit (.number 2304), .lit (.number 2176), .var "\x00119"]) := by rfl

private theorem step_onCurveMul2 (yst : EvmState) (x y : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv x y) (onCurveStateAfterX2 yst x y)
      (.call "\x0016"
        [.lit (.number 2304), .lit (.number 2176), .var "\x00119"])
      (.vals [] (onCurveStateAfterX3 yst x y)) := by
  have hargs := soundArgs (V := onCurveInitialEnv x y)
    (st := onCurveStateAfterX2 yst x y)
    (args := [.lit (.number 2304), .lit (.number 2176), .var "\x00119"])
    (vals := [BitVec.ofNat 256 2304, BitVec.ofNat 256 2176, x]) (by rfl)
  have hcall := Step.callOk hargs lookup_fp2Mul_onCurve (by rfl)
    (step_fp2MulBody (onCurveStateAfterX2 yst x y)
      (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2176) x) (Or.inl rfl)
  simpa [fp2MulDecl, onCurveStateAfterX3] using hcall

theorem exec_onCurveStmt2 (yst : EvmState) (x y : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv x y) (onCurveStateAfterX2 yst x y) onCurveStmt2
      (onCurveInitialEnv x y) (onCurveStateAfterX3 yst x y) .normal := by
  rw [onCurveStmt2_shape]
  exact Step.exprStmt (step_onCurveMul2 yst x y)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
