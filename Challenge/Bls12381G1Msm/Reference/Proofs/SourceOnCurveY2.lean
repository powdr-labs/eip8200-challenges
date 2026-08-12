import Challenge.Bls12381G1Msm.Reference.Proofs.SourceOnCurveDefs

set_option warningAsError true

/-! Relational execution of the `y²` statement in G1MSM `onCurve`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem onCurveStmt0_shape : onCurveStmt0 =
    .letDecl ["\x0091", "\x0092"]
      (some (.call "\x009"
        [.var "\x0088", .var "\x0089", .var "\x0088", .var "\x0089"])) := by
  rfl

def onCurveY2Env (xhi xlo yhi ylo : U256) (yst : EvmState) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ["\x0091", "\x0092"].zip
    [(fpMulResult yst yhi ylo yhi ylo).1,
     (fpMulResult yst yhi ylo yhi ylo).2] ++
    onCurveInitialEnv xhi xlo yhi ylo

def onCurveY2State (yhi ylo : U256) (yst : EvmState) : EvmState :=
  fpMulFinalState yst yhi ylo yhi ylo

theorem step_onCurveY2 (xhi xlo yhi ylo : U256) (yst : EvmState) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv xhi xlo yhi ylo) yst onCurveStmt0
      (onCurveY2Env xhi xlo yhi ylo yst)
      (onCurveY2State yhi ylo yst) .normal := by
  have hyhi : EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv xhi xlo yhi ylo) yst (.var "\x0088")
      (.vals [yhi] yst) := Step.var rfl
  have hylo : EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv xhi xlo yhi ylo) yst (.var "\x0089")
      (.vals [ylo] yst) := Step.var rfl
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv xhi xlo yhi ylo) yst
      [.var "\x0088", .var "\x0089", .var "\x0088", .var "\x0089"]
      (.vals [yhi, ylo, yhi, ylo] yst) :=
    Step.argsCons (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil
      hylo) hyhi) hylo) hyhi
  have hlookup : lookupFun onCurveBodyFuns "\x009" =
      some (fpMulDecl, sourceFuns) := by
    rfl
  have hcall := step_fpMul_of_args yhi ylo yhi ylo hargs hlookup
  rw [onCurveStmt0_shape]
  change ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
    (onCurveInitialEnv xhi xlo yhi ylo) yst
    (.letDecl ["\x0091", "\x0092"]
      (some (.call "\x009"
        [.var "\x0088", .var "\x0089", .var "\x0088", .var "\x0089"])))
    (["\x0091", "\x0092"].zip
      [(fpMulResult yst yhi ylo yhi ylo).1,
       (fpMulResult yst yhi ylo yhi ylo).2] ++
      onCurveInitialEnv xhi xlo yhi ylo)
    (fpMulFinalState yst yhi ylo yhi ylo) .normal
  exact Step.letVal hcall rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
