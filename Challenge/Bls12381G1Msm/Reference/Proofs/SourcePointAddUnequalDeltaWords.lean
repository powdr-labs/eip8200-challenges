import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDeltaInputs

set_option warningAsError true

/-! Low- and high-word assignments for the generic delta subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalDeltaLowEnv (ctx : PointAddUnequalDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalDeltaLeftHiEnv ctx) "fc0_96"
    (pointAddUnequalDeltaRaw ctx).2

def pointAddUnequalDeltaHighEnv (ctx : PointAddUnequalDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalDeltaLowEnv ctx) "fc0_95"
    (pointAddUnequalDeltaRaw ctx).1

private theorem leftHiEnv_leftLo (ctx : PointAddUnequalDeltaContext) :
    VEnv.get (pointAddUnequalDeltaLeftHiEnv ctx) "fc0_99" =
      some (pointAddUnequalDeltaLeftLo ctx) := by
  rw [pointAddUnequalDeltaLeftHiEnv, pointAddUnequalDeltaLeftLoEnv]
  rfl

private theorem leftHiEnv_x3Lo (ctx : PointAddUnequalDeltaContext) :
    VEnv.get (pointAddUnequalDeltaLeftHiEnv ctx) "fc0_97" =
      some ctx.x3Lo := by
  rw [pointAddUnequalDeltaLeftHiEnv, pointAddUnequalDeltaLeftLoEnv,
    pointAddUnequalDeltaHiVarEnv, pointAddUnequalDeltaLoVarEnv]
  rfl

private theorem step_pointAddUnequalDeltaLowExprGeneric
    (ctx : PointAddUnequalDeltaContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalDeltaLeftHiEnv ctx)
      (pointAddUnequalDeltaRawState ctx)
      (.builtin .sub [.var "fc0_99", .var "fc0_97"])
      (.vals [(pointAddUnequalDeltaRaw ctx).2]
        (pointAddUnequalDeltaRawState ctx)) := by
  have hleft : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalDeltaLeftHiEnv ctx)
      (pointAddUnequalDeltaRawState ctx) (.var "fc0_99")
      (.vals [pointAddUnequalDeltaLeftLo ctx]
        (pointAddUnequalDeltaRawState ctx)) :=
    Step.var (leftHiEnv_leftLo ctx)
  have hright : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalDeltaLeftHiEnv ctx)
      (pointAddUnequalDeltaRawState ctx) (.var "fc0_97")
      (.vals [ctx.x3Lo] (pointAddUnequalDeltaRawState ctx)) :=
    Step.var (leftHiEnv_x3Lo ctx)
  have hsub : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalDeltaLeftHiEnv ctx)
      (pointAddUnequalDeltaRawState ctx)
      (.builtin .sub [.var "fc0_99", .var "fc0_97"])
      (.vals [pointAddUnequalDeltaLeftLo ctx - ctx.x3Lo]
        (pointAddUnequalDeltaRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hright) hleft) rfl
  simpa only [pointAddUnequalDeltaRaw, pointAddUnequalDeltaRawLo] using hsub

theorem step_pointAddUnequalDeltaLowGeneric
    (ctx : PointAddUnequalDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalDeltaLeftHiEnv ctx)
      (pointAddUnequalDeltaRawState ctx) pointAddUnequalDeltaRawStmt4
      (pointAddUnequalDeltaLowEnv ctx)
      (pointAddUnequalDeltaRawState ctx) .normal := by
  rw [pointAddUnequalDeltaRawStmt4_eq]
  exact Step.assignVal (step_pointAddUnequalDeltaLowExprGeneric ctx) rfl

private theorem lowEnv_leftHi (ctx : PointAddUnequalDeltaContext) :
    VEnv.get (pointAddUnequalDeltaLowEnv ctx) "fc0_100" =
      some (pointAddUnequalDeltaLeftHi ctx) := by
  rw [pointAddUnequalDeltaLowEnv,
    venv_get_set_ne _ _ _ _ (by decide), pointAddUnequalDeltaLeftHiEnv]
  rfl

private theorem lowEnv_leftLo (ctx : PointAddUnequalDeltaContext) :
    VEnv.get (pointAddUnequalDeltaLowEnv ctx) "fc0_99" =
      some (pointAddUnequalDeltaLeftLo ctx) := by
  rw [pointAddUnequalDeltaLowEnv,
    venv_get_set_ne _ _ _ _ (by decide), pointAddUnequalDeltaLeftHiEnv,
    pointAddUnequalDeltaLeftLoEnv]
  rfl

private theorem lowEnv_x3Hi (ctx : PointAddUnequalDeltaContext) :
    VEnv.get (pointAddUnequalDeltaLowEnv ctx) "fc0_98" =
      some ctx.x3Hi := by
  rw [pointAddUnequalDeltaLowEnv,
    venv_get_set_ne _ _ _ _ (by decide), pointAddUnequalDeltaLeftHiEnv,
    pointAddUnequalDeltaLeftLoEnv, pointAddUnequalDeltaHiVarEnv]
  rfl

private theorem lowEnv_x3Lo (ctx : PointAddUnequalDeltaContext) :
    VEnv.get (pointAddUnequalDeltaLowEnv ctx) "fc0_97" =
      some ctx.x3Lo := by
  rw [pointAddUnequalDeltaLowEnv,
    venv_get_set_ne _ _ _ _ (by decide), pointAddUnequalDeltaLeftHiEnv,
    pointAddUnequalDeltaLeftLoEnv, pointAddUnequalDeltaHiVarEnv,
    pointAddUnequalDeltaLoVarEnv]
  rfl

private theorem step_pointAddUnequalDeltaHighExprGeneric
    (ctx : PointAddUnequalDeltaContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalDeltaLowEnv ctx)
      (pointAddUnequalDeltaRawState ctx)
      (.builtin .sub
        [.builtin .sub [.var "fc0_100", .var "fc0_98"],
         .builtin .gt [.var "fc0_97", .var "fc0_99"]])
      (.vals [(pointAddUnequalDeltaRaw ctx).1]
        (pointAddUnequalDeltaRawState ctx)) := by
  have hleftHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalDeltaLowEnv ctx)
      (pointAddUnequalDeltaRawState ctx) (.var "fc0_100")
      (.vals [pointAddUnequalDeltaLeftHi ctx]
        (pointAddUnequalDeltaRawState ctx)) := Step.var (lowEnv_leftHi ctx)
  have hleftLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalDeltaLowEnv ctx)
      (pointAddUnequalDeltaRawState ctx) (.var "fc0_99")
      (.vals [pointAddUnequalDeltaLeftLo ctx]
        (pointAddUnequalDeltaRawState ctx)) := Step.var (lowEnv_leftLo ctx)
  have hx3Hi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalDeltaLowEnv ctx)
      (pointAddUnequalDeltaRawState ctx) (.var "fc0_98")
      (.vals [ctx.x3Hi] (pointAddUnequalDeltaRawState ctx)) :=
    Step.var (lowEnv_x3Hi ctx)
  have hx3Lo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalDeltaLowEnv ctx)
      (pointAddUnequalDeltaRawState ctx) (.var "fc0_97")
      (.vals [ctx.x3Lo] (pointAddUnequalDeltaRawState ctx)) :=
    Step.var (lowEnv_x3Lo ctx)
  have hborrow : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalDeltaLowEnv ctx)
      (pointAddUnequalDeltaRawState ctx)
      (.builtin .gt [.var "fc0_97", .var "fc0_99"])
      (.vals [b2w (BitVec.ult (pointAddUnequalDeltaLeftLo ctx) ctx.x3Lo)]
        (pointAddUnequalDeltaRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hleftLo) hx3Lo) rfl
  have hinner : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalDeltaLowEnv ctx)
      (pointAddUnequalDeltaRawState ctx)
      (.builtin .sub [.var "fc0_100", .var "fc0_98"])
      (.vals [pointAddUnequalDeltaLeftHi ctx - ctx.x3Hi]
        (pointAddUnequalDeltaRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hx3Hi) hleftHi) rfl
  have hfinal : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalDeltaLowEnv ctx)
      (pointAddUnequalDeltaRawState ctx)
      (.builtin .sub
        [.builtin .sub [.var "fc0_100", .var "fc0_98"],
         .builtin .gt [.var "fc0_97", .var "fc0_99"]])
      (.vals [pointAddUnequalDeltaLeftHi ctx - ctx.x3Hi -
          b2w (BitVec.ult (pointAddUnequalDeltaLeftLo ctx) ctx.x3Lo)]
        (pointAddUnequalDeltaRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hborrow) hinner) rfl
  simpa only [pointAddUnequalDeltaRaw, pointAddUnequalDeltaRawHi] using hfinal

theorem step_pointAddUnequalDeltaHighGeneric
    (ctx : PointAddUnequalDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalDeltaLowEnv ctx)
      (pointAddUnequalDeltaRawState ctx) pointAddUnequalDeltaRawStmt5
      (pointAddUnequalDeltaHighEnv ctx)
      (pointAddUnequalDeltaRawState ctx) .normal := by
  rw [pointAddUnequalDeltaRawStmt5_eq]
  exact Step.assignVal (step_pointAddUnequalDeltaHighExprGeneric ctx) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
