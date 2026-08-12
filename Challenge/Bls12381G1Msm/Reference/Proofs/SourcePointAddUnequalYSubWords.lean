import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalYSubInputs

set_option warningAsError true

/-! Raw low- and high-word assignments for the generic final y subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalYSubLowEnv (ctx : PointAddUnequalYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalYSubHiVarEnv ctx) "fc0_103"
    (pointAddUnequalYSubRaw ctx).2
def pointAddUnequalYSubHighEnv (ctx : PointAddUnequalYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalYSubLowEnv ctx) "fc0_102"
    (pointAddUnequalYSubRaw ctx).1

private theorem hiVarEnv_inputLo (ctx : PointAddUnequalYSubContext) :
    VEnv.get (pointAddUnequalYSubHiVarEnv ctx) "fc0_106" = some ctx.inputLo := by
  rw [pointAddUnequalYSubHiVarEnv]
  exact venv_get_cons_ne _ _ _ _ (by decide)

private theorem hiVarEnv_leftLo (ctx : PointAddUnequalYSubContext) :
    VEnv.get (pointAddUnequalYSubHiVarEnv ctx) "fc0_104" =
      some (pointAddUnequalYSubLeftLo ctx) := by
  rw [pointAddUnequalYSubHiVarEnv, pointAddUnequalYSubLoVarEnv,
    pointAddUnequalYSubLeftHiEnv, pointAddUnequalYSubLeftLoEnv]
  rfl

private theorem step_lowExpr (ctx : PointAddUnequalYSubContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalYSubHiVarEnv ctx)
      (pointAddUnequalYSubRawState ctx)
      (.builtin .sub [.var "fc0_106", .var "fc0_104"])
      (.vals [(pointAddUnequalYSubRaw ctx).2]
        (pointAddUnequalYSubRawState ctx)) := by
  have hinput : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalYSubHiVarEnv ctx)
      (pointAddUnequalYSubRawState ctx) (.var "fc0_106")
      (.vals [ctx.inputLo] (pointAddUnequalYSubRawState ctx)) :=
    Step.var (hiVarEnv_inputLo ctx)
  have hleft : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalYSubHiVarEnv ctx)
      (pointAddUnequalYSubRawState ctx) (.var "fc0_104")
      (.vals [pointAddUnequalYSubLeftLo ctx]
        (pointAddUnequalYSubRawState ctx)) := Step.var (hiVarEnv_leftLo ctx)
  have hsub : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalYSubHiVarEnv ctx)
      (pointAddUnequalYSubRawState ctx)
      (.builtin .sub [.var "fc0_106", .var "fc0_104"])
      (.vals [ctx.inputLo - pointAddUnequalYSubLeftLo ctx]
        (pointAddUnequalYSubRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hleft) hinput) rfl
  simpa only [pointAddUnequalYSubRaw, pointAddUnequalYSubRawLo] using hsub

theorem step_pointAddUnequalYSubLowGeneric (ctx : PointAddUnequalYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalYSubHiVarEnv ctx)
      (pointAddUnequalYSubRawState ctx) pointAddUnequalYSubRawStmt4
      (pointAddUnequalYSubLowEnv ctx) (pointAddUnequalYSubRawState ctx) .normal := by
  rw [pointAddUnequalYSubRawStmt4_eq]
  exact Step.assignVal (step_lowExpr ctx) rfl

private theorem lowEnv_inputHi (ctx : PointAddUnequalYSubContext) :
    VEnv.get (pointAddUnequalYSubLowEnv ctx) "fc0_107" = some ctx.inputHi := by
  rw [pointAddUnequalYSubLowEnv, venv_get_set_ne _ _ _ _ (by decide),
    pointAddUnequalYSubHiVarEnv]
  rfl
private theorem lowEnv_inputLo (ctx : PointAddUnequalYSubContext) :
    VEnv.get (pointAddUnequalYSubLowEnv ctx) "fc0_106" = some ctx.inputLo := by
  rw [pointAddUnequalYSubLowEnv, venv_get_set_ne _ _ _ _ (by decide),
    pointAddUnequalYSubHiVarEnv]
  exact venv_get_cons_ne _ _ _ _ (by decide)
private theorem lowEnv_leftHi (ctx : PointAddUnequalYSubContext) :
    VEnv.get (pointAddUnequalYSubLowEnv ctx) "fc0_105" =
      some (pointAddUnequalYSubLeftHi ctx) := by
  rw [pointAddUnequalYSubLowEnv, venv_get_set_ne _ _ _ _ (by decide),
    pointAddUnequalYSubHiVarEnv, pointAddUnequalYSubLoVarEnv,
    pointAddUnequalYSubLeftHiEnv]
  rfl
private theorem lowEnv_leftLo (ctx : PointAddUnequalYSubContext) :
    VEnv.get (pointAddUnequalYSubLowEnv ctx) "fc0_104" =
      some (pointAddUnequalYSubLeftLo ctx) := by
  rw [pointAddUnequalYSubLowEnv, venv_get_set_ne _ _ _ _ (by decide),
    pointAddUnequalYSubHiVarEnv, pointAddUnequalYSubLoVarEnv,
    pointAddUnequalYSubLeftHiEnv, pointAddUnequalYSubLeftLoEnv]
  rfl

private theorem step_highExpr (ctx : PointAddUnequalYSubContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalYSubLowEnv ctx)
      (pointAddUnequalYSubRawState ctx)
      (.builtin .sub
        [.builtin .sub [.var "fc0_107", .var "fc0_105"],
         .builtin .gt [.var "fc0_104", .var "fc0_106"]])
      (.vals [(pointAddUnequalYSubRaw ctx).1]
        (pointAddUnequalYSubRawState ctx)) := by
  have hinputHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalYSubLowEnv ctx)
      (pointAddUnequalYSubRawState ctx) (.var "fc0_107")
      (.vals [ctx.inputHi] (pointAddUnequalYSubRawState ctx)) :=
    Step.var (lowEnv_inputHi ctx)
  have hinputLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalYSubLowEnv ctx)
      (pointAddUnequalYSubRawState ctx) (.var "fc0_106")
      (.vals [ctx.inputLo] (pointAddUnequalYSubRawState ctx)) :=
    Step.var (lowEnv_inputLo ctx)
  have hleftHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalYSubLowEnv ctx)
      (pointAddUnequalYSubRawState ctx) (.var "fc0_105")
      (.vals [pointAddUnequalYSubLeftHi ctx]
        (pointAddUnequalYSubRawState ctx)) := Step.var (lowEnv_leftHi ctx)
  have hleftLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalYSubLowEnv ctx)
      (pointAddUnequalYSubRawState ctx) (.var "fc0_104")
      (.vals [pointAddUnequalYSubLeftLo ctx]
        (pointAddUnequalYSubRawState ctx)) := Step.var (lowEnv_leftLo ctx)
  have hborrow : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalYSubLowEnv ctx)
      (pointAddUnequalYSubRawState ctx)
      (.builtin .gt [.var "fc0_104", .var "fc0_106"])
      (.vals [b2w (BitVec.ult ctx.inputLo (pointAddUnequalYSubLeftLo ctx))]
        (pointAddUnequalYSubRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hinputLo) hleftLo) rfl
  have hinner : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalYSubLowEnv ctx)
      (pointAddUnequalYSubRawState ctx)
      (.builtin .sub [.var "fc0_107", .var "fc0_105"])
      (.vals [ctx.inputHi - pointAddUnequalYSubLeftHi ctx]
        (pointAddUnequalYSubRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hleftHi) hinputHi) rfl
  have hfinal : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalYSubLowEnv ctx)
      (pointAddUnequalYSubRawState ctx)
      (.builtin .sub
        [.builtin .sub [.var "fc0_107", .var "fc0_105"],
         .builtin .gt [.var "fc0_104", .var "fc0_106"]])
      (.vals [ctx.inputHi - pointAddUnequalYSubLeftHi ctx -
        b2w (BitVec.ult ctx.inputLo (pointAddUnequalYSubLeftLo ctx))]
        (pointAddUnequalYSubRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hborrow) hinner) rfl
  simpa only [pointAddUnequalYSubRaw, pointAddUnequalYSubRawHi] using hfinal

theorem step_pointAddUnequalYSubHighGeneric (ctx : PointAddUnequalYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalYSubLowEnv ctx)
      (pointAddUnequalYSubRawState ctx) pointAddUnequalYSubRawStmt5
      (pointAddUnequalYSubHighEnv ctx) (pointAddUnequalYSubRawState ctx) .normal := by
  rw [pointAddUnequalYSubRawStmt5_eq]
  exact Step.assignVal (step_highExpr ctx) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
