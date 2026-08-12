import Challenge.Bls12381G1Msm.Reference.Proofs.SourceOnCurveY2

set_option warningAsError true

/-! Relational execution of the `x²` statement in G1MSM `onCurve`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem onCurveStmt1_shape : onCurveStmt1 =
    .letDecl ["\x0093", "\x0094"]
      (some (.call "\x009"
        [.var "\x0086", .var "\x0087", .var "\x0086", .var "\x0087"])) := by
  rfl

def onCurveX2Env (xhi xlo yhi ylo : U256) (yst : EvmState) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ["\x0093", "\x0094"].zip
    [(fpMulResult (onCurveY2State yhi ylo yst) xhi xlo xhi xlo).1,
     (fpMulResult (onCurveY2State yhi ylo yst) xhi xlo xhi xlo).2] ++
    onCurveY2Env xhi xlo yhi ylo yst

def onCurveX2State (xhi xlo yhi ylo : U256) (yst : EvmState) : EvmState :=
  fpMulFinalState (onCurveY2State yhi ylo yst) xhi xlo xhi xlo

theorem step_onCurveX2 (xhi xlo yhi ylo : U256) (yst : EvmState) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveY2Env xhi xlo yhi ylo yst)
      (onCurveY2State yhi ylo yst) onCurveStmt1
      (onCurveX2Env xhi xlo yhi ylo yst)
      (onCurveX2State xhi xlo yhi ylo yst) .normal := by
  have hxhi : EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveY2Env xhi xlo yhi ylo yst) (onCurveY2State yhi ylo yst)
      (.var "\x0086") (.vals [xhi] (onCurveY2State yhi ylo yst)) :=
    Step.var rfl
  have hxlo : EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveY2Env xhi xlo yhi ylo yst) (onCurveY2State yhi ylo yst)
      (.var "\x0087") (.vals [xlo] (onCurveY2State yhi ylo yst)) :=
    Step.var rfl
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveY2Env xhi xlo yhi ylo yst) (onCurveY2State yhi ylo yst)
      [.var "\x0086", .var "\x0087", .var "\x0086", .var "\x0087"]
      (.vals [xhi, xlo, xhi, xlo] (onCurveY2State yhi ylo yst)) :=
    Step.argsCons (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil
      hxlo) hxhi) hxlo) hxhi
  have hlookup : lookupFun onCurveBodyFuns "\x009" =
      some (fpMulDecl, sourceFuns) := by
    rfl
  have hcall := step_fpMul_of_args xhi xlo xhi xlo hargs hlookup
  rw [onCurveStmt1_shape]
  change ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
    (onCurveY2Env xhi xlo yhi ylo yst) (onCurveY2State yhi ylo yst)
    (.letDecl ["\x0093", "\x0094"]
      (some (.call "\x009"
        [.var "\x0086", .var "\x0087", .var "\x0086", .var "\x0087"])))
    (["\x0093", "\x0094"].zip
      [(fpMulResult (onCurveY2State yhi ylo yst) xhi xlo xhi xlo).1,
       (fpMulResult (onCurveY2State yhi ylo yst) xhi xlo xhi xlo).2] ++
      onCurveY2Env xhi xlo yhi ylo yst)
    (fpMulFinalState (onCurveY2State yhi ylo yst) xhi xlo xhi xlo) .normal
  exact Step.letVal hcall rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
