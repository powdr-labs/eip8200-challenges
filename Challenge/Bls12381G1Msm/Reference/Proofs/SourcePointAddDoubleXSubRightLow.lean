import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubRightVars

set_option warningAsError true

/-! Generic low-limb assignment of the second point-double x subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleXSubRightLowEnv (ctx : PointAddDoubleXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddDoubleXSubRightHiVarEnv ctx) "fc0_36"
    (pointAddDoubleXSubRightRaw ctx).2

private theorem pointAddDoubleXSubRightHiVarEnv_inputLo
    (ctx : PointAddDoubleXSubRightContext) :
    VEnv.get (pointAddDoubleXSubRightHiVarEnv ctx) "fc0_39" =
      some ctx.x3Lo := by
  rw [pointAddDoubleXSubRightHiVarEnv]
  exact venv_get_cons_ne _ _ _ _ (by decide)

private theorem pointAddDoubleXSubRightHiVarEnv_rightLo
    (ctx : PointAddDoubleXSubRightContext) :
    VEnv.get (pointAddDoubleXSubRightHiVarEnv ctx) "fc0_37" =
      some (pointAddDoubleXSubRightLo ctx) := by
  rw [pointAddDoubleXSubRightHiVarEnv, pointAddDoubleXSubRightLoVarEnv,
    pointAddDoubleXSubRightHiEnv, pointAddDoubleXSubRightLoEnv]
  rfl

private theorem step_pointAddDoubleXSubRightLowExprGeneric
    (ctx : PointAddDoubleXSubRightContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleXSubRightHiVarEnv ctx)
      (pointAddDoubleXSubRightRawState ctx)
      (.builtin .sub [.var "fc0_39", .var "fc0_37"])
      (.vals [(pointAddDoubleXSubRightRaw ctx).2]
        (pointAddDoubleXSubRightRawState ctx)) := by
  have hinput : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleXSubRightHiVarEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) (.var "fc0_39")
      (.vals [ctx.x3Lo] (pointAddDoubleXSubRightRawState ctx)) :=
    Step.var (pointAddDoubleXSubRightHiVarEnv_inputLo ctx)
  have hright : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleXSubRightHiVarEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) (.var "fc0_37")
      (.vals [pointAddDoubleXSubRightLo ctx]
        (pointAddDoubleXSubRightRawState ctx)) :=
    Step.var (pointAddDoubleXSubRightHiVarEnv_rightLo ctx)
  have hsub : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleXSubRightHiVarEnv ctx)
      (pointAddDoubleXSubRightRawState ctx)
      (.builtin .sub [.var "fc0_39", .var "fc0_37"])
      (.vals [ctx.x3Lo - pointAddDoubleXSubRightLo ctx]
        (pointAddDoubleXSubRightRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hright) hinput) rfl
  simpa only [pointAddDoubleXSubRightRaw, pointAddDoubleXSubRightRawLo]
    using hsub

theorem step_pointAddDoubleXSubRightLowGeneric
    (ctx : PointAddDoubleXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleXSubRightHiVarEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) pointAddDoubleXSubRightRawStmt4
      (pointAddDoubleXSubRightLowEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) .normal := by
  rw [pointAddDoubleXSubRightRawStmt4_eq]
  exact Step.assignVal (step_pointAddDoubleXSubRightLowExprGeneric ctx) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
