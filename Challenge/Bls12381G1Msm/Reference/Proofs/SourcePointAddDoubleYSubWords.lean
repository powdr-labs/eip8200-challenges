import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleYSubInputs

set_option warningAsError true

/-! Raw low- and high-word assignments for the generic final y subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleYSubLowEnv (ctx : PointAddDoubleYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddDoubleYSubHiVarEnv ctx) "fc0_50"
    (pointAddDoubleYSubRaw ctx).2
def pointAddDoubleYSubHighEnv (ctx : PointAddDoubleYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddDoubleYSubLowEnv ctx) "fc0_49"
    (pointAddDoubleYSubRaw ctx).1

private theorem hiVarEnv_inputLo (ctx : PointAddDoubleYSubContext) :
    VEnv.get (pointAddDoubleYSubHiVarEnv ctx) "fc0_53" = some ctx.inputLo := by
  rw [pointAddDoubleYSubHiVarEnv]
  exact venv_get_cons_ne _ _ _ _ (by decide)

private theorem hiVarEnv_leftLo (ctx : PointAddDoubleYSubContext) :
    VEnv.get (pointAddDoubleYSubHiVarEnv ctx) "fc0_51" =
      some (pointAddDoubleYSubLeftLo ctx) := by
  rw [pointAddDoubleYSubHiVarEnv, pointAddDoubleYSubLoVarEnv,
    pointAddDoubleYSubLeftHiEnv, pointAddDoubleYSubLeftLoEnv]
  rfl

private theorem step_lowExpr (ctx : PointAddDoubleYSubContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleYSubHiVarEnv ctx)
      (pointAddDoubleYSubRawState ctx)
      (.builtin .sub [.var "fc0_53", .var "fc0_51"])
      (.vals [(pointAddDoubleYSubRaw ctx).2]
        (pointAddDoubleYSubRawState ctx)) := by
  have hinput : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleYSubHiVarEnv ctx)
      (pointAddDoubleYSubRawState ctx) (.var "fc0_53")
      (.vals [ctx.inputLo] (pointAddDoubleYSubRawState ctx)) :=
    Step.var (hiVarEnv_inputLo ctx)
  have hleft : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleYSubHiVarEnv ctx)
      (pointAddDoubleYSubRawState ctx) (.var "fc0_51")
      (.vals [pointAddDoubleYSubLeftLo ctx]
        (pointAddDoubleYSubRawState ctx)) := Step.var (hiVarEnv_leftLo ctx)
  have hsub : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleYSubHiVarEnv ctx)
      (pointAddDoubleYSubRawState ctx)
      (.builtin .sub [.var "fc0_53", .var "fc0_51"])
      (.vals [ctx.inputLo - pointAddDoubleYSubLeftLo ctx]
        (pointAddDoubleYSubRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hleft) hinput) rfl
  simpa only [pointAddDoubleYSubRaw, pointAddDoubleYSubRawLo] using hsub

theorem step_pointAddDoubleYSubLowGeneric (ctx : PointAddDoubleYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleYSubHiVarEnv ctx)
      (pointAddDoubleYSubRawState ctx) pointAddDoubleYSubRawStmt4
      (pointAddDoubleYSubLowEnv ctx) (pointAddDoubleYSubRawState ctx) .normal := by
  rw [pointAddDoubleYSubRawStmt4_eq]
  exact Step.assignVal (step_lowExpr ctx) rfl

private theorem lowEnv_inputHi (ctx : PointAddDoubleYSubContext) :
    VEnv.get (pointAddDoubleYSubLowEnv ctx) "fc0_54" = some ctx.inputHi := by
  rw [pointAddDoubleYSubLowEnv, venv_get_set_ne _ _ _ _ (by decide),
    pointAddDoubleYSubHiVarEnv]
  rfl
private theorem lowEnv_inputLo (ctx : PointAddDoubleYSubContext) :
    VEnv.get (pointAddDoubleYSubLowEnv ctx) "fc0_53" = some ctx.inputLo := by
  rw [pointAddDoubleYSubLowEnv, venv_get_set_ne _ _ _ _ (by decide),
    pointAddDoubleYSubHiVarEnv]
  exact venv_get_cons_ne _ _ _ _ (by decide)
private theorem lowEnv_leftHi (ctx : PointAddDoubleYSubContext) :
    VEnv.get (pointAddDoubleYSubLowEnv ctx) "fc0_52" =
      some (pointAddDoubleYSubLeftHi ctx) := by
  rw [pointAddDoubleYSubLowEnv, venv_get_set_ne _ _ _ _ (by decide),
    pointAddDoubleYSubHiVarEnv, pointAddDoubleYSubLoVarEnv,
    pointAddDoubleYSubLeftHiEnv]
  rfl
private theorem lowEnv_leftLo (ctx : PointAddDoubleYSubContext) :
    VEnv.get (pointAddDoubleYSubLowEnv ctx) "fc0_51" =
      some (pointAddDoubleYSubLeftLo ctx) := by
  rw [pointAddDoubleYSubLowEnv, venv_get_set_ne _ _ _ _ (by decide),
    pointAddDoubleYSubHiVarEnv, pointAddDoubleYSubLoVarEnv,
    pointAddDoubleYSubLeftHiEnv, pointAddDoubleYSubLeftLoEnv]
  rfl

private theorem step_highExpr (ctx : PointAddDoubleYSubContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleYSubLowEnv ctx)
      (pointAddDoubleYSubRawState ctx)
      (.builtin .sub
        [.builtin .sub [.var "fc0_54", .var "fc0_52"],
         .builtin .gt [.var "fc0_51", .var "fc0_53"]])
      (.vals [(pointAddDoubleYSubRaw ctx).1]
        (pointAddDoubleYSubRawState ctx)) := by
  have hinputHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleYSubLowEnv ctx)
      (pointAddDoubleYSubRawState ctx) (.var "fc0_54")
      (.vals [ctx.inputHi] (pointAddDoubleYSubRawState ctx)) :=
    Step.var (lowEnv_inputHi ctx)
  have hinputLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleYSubLowEnv ctx)
      (pointAddDoubleYSubRawState ctx) (.var "fc0_53")
      (.vals [ctx.inputLo] (pointAddDoubleYSubRawState ctx)) :=
    Step.var (lowEnv_inputLo ctx)
  have hleftHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleYSubLowEnv ctx)
      (pointAddDoubleYSubRawState ctx) (.var "fc0_52")
      (.vals [pointAddDoubleYSubLeftHi ctx]
        (pointAddDoubleYSubRawState ctx)) := Step.var (lowEnv_leftHi ctx)
  have hleftLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleYSubLowEnv ctx)
      (pointAddDoubleYSubRawState ctx) (.var "fc0_51")
      (.vals [pointAddDoubleYSubLeftLo ctx]
        (pointAddDoubleYSubRawState ctx)) := Step.var (lowEnv_leftLo ctx)
  have hborrow : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleYSubLowEnv ctx)
      (pointAddDoubleYSubRawState ctx)
      (.builtin .gt [.var "fc0_51", .var "fc0_53"])
      (.vals [b2w (BitVec.ult ctx.inputLo (pointAddDoubleYSubLeftLo ctx))]
        (pointAddDoubleYSubRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hinputLo) hleftLo) rfl
  have hinner : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleYSubLowEnv ctx)
      (pointAddDoubleYSubRawState ctx)
      (.builtin .sub [.var "fc0_54", .var "fc0_52"])
      (.vals [ctx.inputHi - pointAddDoubleYSubLeftHi ctx]
        (pointAddDoubleYSubRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hleftHi) hinputHi) rfl
  have hfinal : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleYSubLowEnv ctx)
      (pointAddDoubleYSubRawState ctx)
      (.builtin .sub
        [.builtin .sub [.var "fc0_54", .var "fc0_52"],
         .builtin .gt [.var "fc0_51", .var "fc0_53"]])
      (.vals [ctx.inputHi - pointAddDoubleYSubLeftHi ctx -
        b2w (BitVec.ult ctx.inputLo (pointAddDoubleYSubLeftLo ctx))]
        (pointAddDoubleYSubRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hborrow) hinner) rfl
  simpa only [pointAddDoubleYSubRaw, pointAddDoubleYSubRawHi] using hfinal

theorem step_pointAddDoubleYSubHighGeneric (ctx : PointAddDoubleYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleYSubLowEnv ctx)
      (pointAddDoubleYSubRawState ctx) pointAddDoubleYSubRawStmt5
      (pointAddDoubleYSubHighEnv ctx) (pointAddDoubleYSubRawState ctx) .normal := by
  rw [pointAddDoubleYSubRawStmt5_eq]
  exact Step.assignVal (step_highExpr ctx) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
