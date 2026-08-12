import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubRightLow

set_option warningAsError true

/-! Generic high-limb assignment of the second point-double x subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleXSubRightHighEnv (ctx : PointAddDoubleXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddDoubleXSubRightLowEnv ctx) "fc0_35"
    (pointAddDoubleXSubRightRaw ctx).1

private theorem lowEnv_inputHi (ctx : PointAddDoubleXSubRightContext) :
    VEnv.get (pointAddDoubleXSubRightLowEnv ctx) "fc0_40" = some ctx.x3Hi := by
  rw [pointAddDoubleXSubRightLowEnv,
    venv_get_set_ne _ _ _ _ (by decide), pointAddDoubleXSubRightHiVarEnv]
  rfl

private theorem lowEnv_inputLo (ctx : PointAddDoubleXSubRightContext) :
    VEnv.get (pointAddDoubleXSubRightLowEnv ctx) "fc0_39" = some ctx.x3Lo := by
  rw [pointAddDoubleXSubRightLowEnv,
    venv_get_set_ne _ _ _ _ (by decide), pointAddDoubleXSubRightHiVarEnv]
  exact venv_get_cons_ne _ _ _ _ (by decide)

private theorem lowEnv_rightHi (ctx : PointAddDoubleXSubRightContext) :
    VEnv.get (pointAddDoubleXSubRightLowEnv ctx) "fc0_38" =
      some (pointAddDoubleXSubRightHi ctx) := by
  rw [pointAddDoubleXSubRightLowEnv,
    venv_get_set_ne _ _ _ _ (by decide), pointAddDoubleXSubRightHiVarEnv,
    pointAddDoubleXSubRightLoVarEnv, pointAddDoubleXSubRightHiEnv]
  rfl

private theorem lowEnv_rightLo (ctx : PointAddDoubleXSubRightContext) :
    VEnv.get (pointAddDoubleXSubRightLowEnv ctx) "fc0_37" =
      some (pointAddDoubleXSubRightLo ctx) := by
  rw [pointAddDoubleXSubRightLowEnv,
    venv_get_set_ne _ _ _ _ (by decide), pointAddDoubleXSubRightHiVarEnv,
    pointAddDoubleXSubRightLoVarEnv, pointAddDoubleXSubRightHiEnv,
    pointAddDoubleXSubRightLoEnv]
  rfl

private theorem step_pointAddDoubleXSubRightHighExprGeneric
    (ctx : PointAddDoubleXSubRightContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleXSubRightLowEnv ctx)
      (pointAddDoubleXSubRightRawState ctx)
      (.builtin .sub
        [.builtin .sub [.var "fc0_40", .var "fc0_38"],
         .builtin .gt [.var "fc0_37", .var "fc0_39"]])
      (.vals [(pointAddDoubleXSubRightRaw ctx).1]
        (pointAddDoubleXSubRightRawState ctx)) := by
  have hinputHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleXSubRightLowEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) (.var "fc0_40")
      (.vals [ctx.x3Hi] (pointAddDoubleXSubRightRawState ctx)) :=
    Step.var (lowEnv_inputHi ctx)
  have hinputLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleXSubRightLowEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) (.var "fc0_39")
      (.vals [ctx.x3Lo] (pointAddDoubleXSubRightRawState ctx)) :=
    Step.var (lowEnv_inputLo ctx)
  have hrightHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleXSubRightLowEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) (.var "fc0_38")
      (.vals [pointAddDoubleXSubRightHi ctx]
        (pointAddDoubleXSubRightRawState ctx)) :=
    Step.var (lowEnv_rightHi ctx)
  have hrightLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleXSubRightLowEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) (.var "fc0_37")
      (.vals [pointAddDoubleXSubRightLo ctx]
        (pointAddDoubleXSubRightRawState ctx)) :=
    Step.var (lowEnv_rightLo ctx)
  have hborrow : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleXSubRightLowEnv ctx)
      (pointAddDoubleXSubRightRawState ctx)
      (.builtin .gt [.var "fc0_37", .var "fc0_39"])
      (.vals [b2w (BitVec.ult ctx.x3Lo (pointAddDoubleXSubRightLo ctx))]
        (pointAddDoubleXSubRightRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hinputLo) hrightLo) rfl
  have hinner : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleXSubRightLowEnv ctx)
      (pointAddDoubleXSubRightRawState ctx)
      (.builtin .sub [.var "fc0_40", .var "fc0_38"])
      (.vals [ctx.x3Hi - pointAddDoubleXSubRightHi ctx]
        (pointAddDoubleXSubRightRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hrightHi) hinputHi) rfl
  have hfinal : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleXSubRightLowEnv ctx)
      (pointAddDoubleXSubRightRawState ctx)
      (.builtin .sub
        [.builtin .sub [.var "fc0_40", .var "fc0_38"],
         .builtin .gt [.var "fc0_37", .var "fc0_39"]])
      (.vals [ctx.x3Hi - pointAddDoubleXSubRightHi ctx -
          b2w (BitVec.ult ctx.x3Lo (pointAddDoubleXSubRightLo ctx))]
        (pointAddDoubleXSubRightRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hborrow) hinner) rfl
  simpa only [pointAddDoubleXSubRightRaw, pointAddDoubleXSubRightRawHi]
    using hfinal

theorem step_pointAddDoubleXSubRightHighGeneric
    (ctx : PointAddDoubleXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleXSubRightLowEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) pointAddDoubleXSubRightRawStmt5
      (pointAddDoubleXSubRightHighEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) .normal := by
  rw [pointAddDoubleXSubRightRawStmt5_eq]
  exact Step.assignVal (step_pointAddDoubleXSubRightHighExprGeneric ctx) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
