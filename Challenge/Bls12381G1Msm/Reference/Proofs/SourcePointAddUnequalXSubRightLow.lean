import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubRightVars

set_option warningAsError true

/-! Generic low-limb assignment of the second unequal-point x subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalXSubRightLowEnv (ctx : PointAddUnequalXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalXSubRightHiVarEnv ctx) "fc0_89"
    (pointAddUnequalXSubRightRaw ctx).2

private theorem pointAddUnequalXSubRightHiVarEnv_inputLo
    (ctx : PointAddUnequalXSubRightContext) :
    VEnv.get (pointAddUnequalXSubRightHiVarEnv ctx) "fc0_92" =
      some ctx.x3Lo := by
  rw [pointAddUnequalXSubRightHiVarEnv]
  exact venv_get_cons_ne _ _ _ _ (by decide)

private theorem pointAddUnequalXSubRightHiVarEnv_rightLo
    (ctx : PointAddUnequalXSubRightContext) :
    VEnv.get (pointAddUnequalXSubRightHiVarEnv ctx) "fc0_90" =
      some (pointAddUnequalXSubRightLo ctx) := by
  rw [pointAddUnequalXSubRightHiVarEnv, pointAddUnequalXSubRightLoVarEnv,
    pointAddUnequalXSubRightHiEnv, pointAddUnequalXSubRightLoEnv]
  rfl

private theorem step_pointAddUnequalXSubRightLowExprGeneric
    (ctx : PointAddUnequalXSubRightContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalXSubRightHiVarEnv ctx)
      (pointAddUnequalXSubRightRawState ctx)
      (.builtin .sub [.var "fc0_92", .var "fc0_90"])
      (.vals [(pointAddUnequalXSubRightRaw ctx).2]
        (pointAddUnequalXSubRightRawState ctx)) := by
  have hinput : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalXSubRightHiVarEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) (.var "fc0_92")
      (.vals [ctx.x3Lo] (pointAddUnequalXSubRightRawState ctx)) :=
    Step.var (pointAddUnequalXSubRightHiVarEnv_inputLo ctx)
  have hright : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalXSubRightHiVarEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) (.var "fc0_90")
      (.vals [pointAddUnequalXSubRightLo ctx]
        (pointAddUnequalXSubRightRawState ctx)) :=
    Step.var (pointAddUnequalXSubRightHiVarEnv_rightLo ctx)
  have hsub : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalXSubRightHiVarEnv ctx)
      (pointAddUnequalXSubRightRawState ctx)
      (.builtin .sub [.var "fc0_92", .var "fc0_90"])
      (.vals [ctx.x3Lo - pointAddUnequalXSubRightLo ctx]
        (pointAddUnequalXSubRightRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hright) hinput) rfl
  simpa only [pointAddUnequalXSubRightRaw, pointAddUnequalXSubRightRawLo]
    using hsub

theorem step_pointAddUnequalXSubRightLowGeneric
    (ctx : PointAddUnequalXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalXSubRightHiVarEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) pointAddUnequalXSubRightRawStmt4
      (pointAddUnequalXSubRightLowEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) .normal := by
  rw [pointAddUnequalXSubRightRawStmt4_eq]
  exact Step.assignVal (step_pointAddUnequalXSubRightLowExprGeneric ctx) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
