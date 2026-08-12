import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleDeltaInputs

set_option warningAsError true

/-! Low- and high-word assignments for the generic delta subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleDeltaLowEnv (ctx : PointAddDoubleDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddDoubleDeltaLeftHiEnv ctx) "fc0_43"
    (pointAddDoubleDeltaRaw ctx).2

def pointAddDoubleDeltaHighEnv (ctx : PointAddDoubleDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddDoubleDeltaLowEnv ctx) "fc0_42"
    (pointAddDoubleDeltaRaw ctx).1

private theorem leftHiEnv_leftLo (ctx : PointAddDoubleDeltaContext) :
    VEnv.get (pointAddDoubleDeltaLeftHiEnv ctx) "fc0_46" =
      some (pointAddDoubleDeltaLeftLo ctx) := by
  rw [pointAddDoubleDeltaLeftHiEnv, pointAddDoubleDeltaLeftLoEnv]
  rfl

private theorem leftHiEnv_x3Lo (ctx : PointAddDoubleDeltaContext) :
    VEnv.get (pointAddDoubleDeltaLeftHiEnv ctx) "fc0_44" =
      some ctx.x3Lo := by
  rw [pointAddDoubleDeltaLeftHiEnv, pointAddDoubleDeltaLeftLoEnv,
    pointAddDoubleDeltaHiVarEnv, pointAddDoubleDeltaLoVarEnv]
  rfl

private theorem step_pointAddDoubleDeltaLowExprGeneric
    (ctx : PointAddDoubleDeltaContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleDeltaLeftHiEnv ctx)
      (pointAddDoubleDeltaRawState ctx)
      (.builtin .sub [.var "fc0_46", .var "fc0_44"])
      (.vals [(pointAddDoubleDeltaRaw ctx).2]
        (pointAddDoubleDeltaRawState ctx)) := by
  have hleft : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleDeltaLeftHiEnv ctx)
      (pointAddDoubleDeltaRawState ctx) (.var "fc0_46")
      (.vals [pointAddDoubleDeltaLeftLo ctx]
        (pointAddDoubleDeltaRawState ctx)) :=
    Step.var (leftHiEnv_leftLo ctx)
  have hright : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleDeltaLeftHiEnv ctx)
      (pointAddDoubleDeltaRawState ctx) (.var "fc0_44")
      (.vals [ctx.x3Lo] (pointAddDoubleDeltaRawState ctx)) :=
    Step.var (leftHiEnv_x3Lo ctx)
  have hsub : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleDeltaLeftHiEnv ctx)
      (pointAddDoubleDeltaRawState ctx)
      (.builtin .sub [.var "fc0_46", .var "fc0_44"])
      (.vals [pointAddDoubleDeltaLeftLo ctx - ctx.x3Lo]
        (pointAddDoubleDeltaRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hright) hleft) rfl
  simpa only [pointAddDoubleDeltaRaw, pointAddDoubleDeltaRawLo] using hsub

theorem step_pointAddDoubleDeltaLowGeneric
    (ctx : PointAddDoubleDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleDeltaLeftHiEnv ctx)
      (pointAddDoubleDeltaRawState ctx) pointAddDoubleDeltaRawStmt4
      (pointAddDoubleDeltaLowEnv ctx)
      (pointAddDoubleDeltaRawState ctx) .normal := by
  rw [pointAddDoubleDeltaRawStmt4_eq]
  exact Step.assignVal (step_pointAddDoubleDeltaLowExprGeneric ctx) rfl

private theorem lowEnv_leftHi (ctx : PointAddDoubleDeltaContext) :
    VEnv.get (pointAddDoubleDeltaLowEnv ctx) "fc0_47" =
      some (pointAddDoubleDeltaLeftHi ctx) := by
  rw [pointAddDoubleDeltaLowEnv,
    venv_get_set_ne _ _ _ _ (by decide), pointAddDoubleDeltaLeftHiEnv]
  rfl

private theorem lowEnv_leftLo (ctx : PointAddDoubleDeltaContext) :
    VEnv.get (pointAddDoubleDeltaLowEnv ctx) "fc0_46" =
      some (pointAddDoubleDeltaLeftLo ctx) := by
  rw [pointAddDoubleDeltaLowEnv,
    venv_get_set_ne _ _ _ _ (by decide), pointAddDoubleDeltaLeftHiEnv,
    pointAddDoubleDeltaLeftLoEnv]
  rfl

private theorem lowEnv_x3Hi (ctx : PointAddDoubleDeltaContext) :
    VEnv.get (pointAddDoubleDeltaLowEnv ctx) "fc0_45" =
      some ctx.x3Hi := by
  rw [pointAddDoubleDeltaLowEnv,
    venv_get_set_ne _ _ _ _ (by decide), pointAddDoubleDeltaLeftHiEnv,
    pointAddDoubleDeltaLeftLoEnv, pointAddDoubleDeltaHiVarEnv]
  rfl

private theorem lowEnv_x3Lo (ctx : PointAddDoubleDeltaContext) :
    VEnv.get (pointAddDoubleDeltaLowEnv ctx) "fc0_44" =
      some ctx.x3Lo := by
  rw [pointAddDoubleDeltaLowEnv,
    venv_get_set_ne _ _ _ _ (by decide), pointAddDoubleDeltaLeftHiEnv,
    pointAddDoubleDeltaLeftLoEnv, pointAddDoubleDeltaHiVarEnv,
    pointAddDoubleDeltaLoVarEnv]
  rfl

private theorem step_pointAddDoubleDeltaHighExprGeneric
    (ctx : PointAddDoubleDeltaContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleDeltaLowEnv ctx)
      (pointAddDoubleDeltaRawState ctx)
      (.builtin .sub
        [.builtin .sub [.var "fc0_47", .var "fc0_45"],
         .builtin .gt [.var "fc0_44", .var "fc0_46"]])
      (.vals [(pointAddDoubleDeltaRaw ctx).1]
        (pointAddDoubleDeltaRawState ctx)) := by
  have hleftHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleDeltaLowEnv ctx)
      (pointAddDoubleDeltaRawState ctx) (.var "fc0_47")
      (.vals [pointAddDoubleDeltaLeftHi ctx]
        (pointAddDoubleDeltaRawState ctx)) := Step.var (lowEnv_leftHi ctx)
  have hleftLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleDeltaLowEnv ctx)
      (pointAddDoubleDeltaRawState ctx) (.var "fc0_46")
      (.vals [pointAddDoubleDeltaLeftLo ctx]
        (pointAddDoubleDeltaRawState ctx)) := Step.var (lowEnv_leftLo ctx)
  have hx3Hi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleDeltaLowEnv ctx)
      (pointAddDoubleDeltaRawState ctx) (.var "fc0_45")
      (.vals [ctx.x3Hi] (pointAddDoubleDeltaRawState ctx)) :=
    Step.var (lowEnv_x3Hi ctx)
  have hx3Lo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleDeltaLowEnv ctx)
      (pointAddDoubleDeltaRawState ctx) (.var "fc0_44")
      (.vals [ctx.x3Lo] (pointAddDoubleDeltaRawState ctx)) :=
    Step.var (lowEnv_x3Lo ctx)
  have hborrow : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleDeltaLowEnv ctx)
      (pointAddDoubleDeltaRawState ctx)
      (.builtin .gt [.var "fc0_44", .var "fc0_46"])
      (.vals [b2w (BitVec.ult (pointAddDoubleDeltaLeftLo ctx) ctx.x3Lo)]
        (pointAddDoubleDeltaRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hleftLo) hx3Lo) rfl
  have hinner : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleDeltaLowEnv ctx)
      (pointAddDoubleDeltaRawState ctx)
      (.builtin .sub [.var "fc0_47", .var "fc0_45"])
      (.vals [pointAddDoubleDeltaLeftHi ctx - ctx.x3Hi]
        (pointAddDoubleDeltaRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hx3Hi) hleftHi) rfl
  have hfinal : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleDeltaLowEnv ctx)
      (pointAddDoubleDeltaRawState ctx)
      (.builtin .sub
        [.builtin .sub [.var "fc0_47", .var "fc0_45"],
         .builtin .gt [.var "fc0_44", .var "fc0_46"]])
      (.vals [pointAddDoubleDeltaLeftHi ctx - ctx.x3Hi -
          b2w (BitVec.ult (pointAddDoubleDeltaLeftLo ctx) ctx.x3Lo)]
        (pointAddDoubleDeltaRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hborrow) hinner) rfl
  simpa only [pointAddDoubleDeltaRaw, pointAddDoubleDeltaRawHi] using hfinal

theorem step_pointAddDoubleDeltaHighGeneric
    (ctx : PointAddDoubleDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleDeltaLowEnv ctx)
      (pointAddDoubleDeltaRawState ctx) pointAddDoubleDeltaRawStmt5
      (pointAddDoubleDeltaHighEnv ctx)
      (pointAddDoubleDeltaRawState ctx) .normal := by
  rw [pointAddDoubleDeltaRawStmt5_eq]
  exact Step.assignVal (step_pointAddDoubleDeltaHighExprGeneric ctx) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
