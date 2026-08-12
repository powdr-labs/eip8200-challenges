import Challenge.Bls12381G1Msm.Reference.Proofs.SourceOnCurveX2

set_option warningAsError true

/-! Relational execution of the `x³` statement in G1MSM `onCurve`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem onCurveStmt2_shape : onCurveStmt2 =
    .letDecl ["\x0095", "\x0096"]
      (some (.call "\x009"
        [.var "\x0093", .var "\x0094", .var "\x0086", .var "\x0087"])) := by
  rfl

def onCurveX3Env (xhi xlo yhi ylo : U256) (yst : EvmState) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  let x2 := fpMulResult (onCurveY2State yhi ylo yst) xhi xlo xhi xlo
  ["\x0095", "\x0096"].zip
    [(fpMulResult (onCurveX2State xhi xlo yhi ylo yst)
      x2.1 x2.2 xhi xlo).1,
     (fpMulResult (onCurveX2State xhi xlo yhi ylo yst)
      x2.1 x2.2 xhi xlo).2] ++
    onCurveX2Env xhi xlo yhi ylo yst

def onCurveX3State (xhi xlo yhi ylo : U256) (yst : EvmState) : EvmState :=
  let x2 := fpMulResult (onCurveY2State yhi ylo yst) xhi xlo xhi xlo
  fpMulFinalState (onCurveX2State xhi xlo yhi ylo yst)
    x2.1 x2.2 xhi xlo

theorem step_onCurveX3 (xhi xlo yhi ylo : U256) (yst : EvmState) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveX2Env xhi xlo yhi ylo yst)
      (onCurveX2State xhi xlo yhi ylo yst) onCurveStmt2
      (onCurveX3Env xhi xlo yhi ylo yst)
      (onCurveX3State xhi xlo yhi ylo yst) .normal := by
  let x2 := fpMulResult (onCurveY2State yhi ylo yst) xhi xlo xhi xlo
  have hx2hi : EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveX2Env xhi xlo yhi ylo yst)
      (onCurveX2State xhi xlo yhi ylo yst) (.var "\x0093")
      (.vals [x2.1] (onCurveX2State xhi xlo yhi ylo yst)) := Step.var rfl
  have hx2lo : EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveX2Env xhi xlo yhi ylo yst)
      (onCurveX2State xhi xlo yhi ylo yst) (.var "\x0094")
      (.vals [x2.2] (onCurveX2State xhi xlo yhi ylo yst)) := Step.var rfl
  have hxhi : EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveX2Env xhi xlo yhi ylo yst)
      (onCurveX2State xhi xlo yhi ylo yst) (.var "\x0086")
      (.vals [xhi] (onCurveX2State xhi xlo yhi ylo yst)) := Step.var rfl
  have hxlo : EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveX2Env xhi xlo yhi ylo yst)
      (onCurveX2State xhi xlo yhi ylo yst) (.var "\x0087")
      (.vals [xlo] (onCurveX2State xhi xlo yhi ylo yst)) := Step.var rfl
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveX2Env xhi xlo yhi ylo yst)
      (onCurveX2State xhi xlo yhi ylo yst)
      [.var "\x0093", .var "\x0094", .var "\x0086", .var "\x0087"]
      (.vals [x2.1, x2.2, xhi, xlo]
        (onCurveX2State xhi xlo yhi ylo yst)) :=
    Step.argsCons (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil
      hxlo) hxhi) hx2lo) hx2hi
  have hlookup : lookupFun onCurveBodyFuns "\x009" =
      some (fpMulDecl, sourceFuns) := by
    rfl
  have hcall := step_fpMul_of_args x2.1 x2.2 xhi xlo hargs hlookup
  rw [onCurveStmt2_shape]
  change ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
    (onCurveX2Env xhi xlo yhi ylo yst)
    (onCurveX2State xhi xlo yhi ylo yst)
    (.letDecl ["\x0095", "\x0096"]
      (some (.call "\x009"
        [.var "\x0093", .var "\x0094", .var "\x0086", .var "\x0087"])))
    (["\x0095", "\x0096"].zip
      [(fpMulResult (onCurveX2State xhi xlo yhi ylo yst)
        x2.1 x2.2 xhi xlo).1,
       (fpMulResult (onCurveX2State xhi xlo yhi ylo yst)
        x2.1 x2.2 xhi xlo).2] ++
      onCurveX2Env xhi xlo yhi ylo yst)
    (fpMulFinalState (onCurveX2State xhi xlo yhi ylo yst)
      x2.1 x2.2 xhi xlo) .normal
  exact Step.letVal hcall rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
