import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubRightLow

set_option warningAsError true

/-! Generic high-limb assignment of the second unequal-point x subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalXSubRightHighEnv (ctx : PointAddUnequalXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalXSubRightLowEnv ctx) "fc0_88"
    (pointAddUnequalXSubRightRaw ctx).1

private theorem lowEnv_inputHi (ctx : PointAddUnequalXSubRightContext) :
    VEnv.get (pointAddUnequalXSubRightLowEnv ctx) "fc0_93" = some ctx.x3Hi := by
  rw [pointAddUnequalXSubRightLowEnv,
    venv_get_set_ne _ _ _ _ (by decide), pointAddUnequalXSubRightHiVarEnv]
  rfl

private theorem lowEnv_inputLo (ctx : PointAddUnequalXSubRightContext) :
    VEnv.get (pointAddUnequalXSubRightLowEnv ctx) "fc0_92" = some ctx.x3Lo := by
  rw [pointAddUnequalXSubRightLowEnv,
    venv_get_set_ne _ _ _ _ (by decide), pointAddUnequalXSubRightHiVarEnv]
  exact venv_get_cons_ne _ _ _ _ (by decide)

private theorem lowEnv_rightHi (ctx : PointAddUnequalXSubRightContext) :
    VEnv.get (pointAddUnequalXSubRightLowEnv ctx) "fc0_91" =
      some (pointAddUnequalXSubRightHi ctx) := by
  rw [pointAddUnequalXSubRightLowEnv,
    venv_get_set_ne _ _ _ _ (by decide), pointAddUnequalXSubRightHiVarEnv,
    pointAddUnequalXSubRightLoVarEnv, pointAddUnequalXSubRightHiEnv]
  rfl

private theorem lowEnv_rightLo (ctx : PointAddUnequalXSubRightContext) :
    VEnv.get (pointAddUnequalXSubRightLowEnv ctx) "fc0_90" =
      some (pointAddUnequalXSubRightLo ctx) := by
  rw [pointAddUnequalXSubRightLowEnv,
    venv_get_set_ne _ _ _ _ (by decide), pointAddUnequalXSubRightHiVarEnv,
    pointAddUnequalXSubRightLoVarEnv, pointAddUnequalXSubRightHiEnv,
    pointAddUnequalXSubRightLoEnv]
  rfl

private theorem step_pointAddUnequalXSubRightHighExprGeneric
    (ctx : PointAddUnequalXSubRightContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalXSubRightLowEnv ctx)
      (pointAddUnequalXSubRightRawState ctx)
      (.builtin .sub
        [.builtin .sub [.var "fc0_93", .var "fc0_91"],
         .builtin .gt [.var "fc0_90", .var "fc0_92"]])
      (.vals [(pointAddUnequalXSubRightRaw ctx).1]
        (pointAddUnequalXSubRightRawState ctx)) := by
  have hinputHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalXSubRightLowEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) (.var "fc0_93")
      (.vals [ctx.x3Hi] (pointAddUnequalXSubRightRawState ctx)) :=
    Step.var (lowEnv_inputHi ctx)
  have hinputLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalXSubRightLowEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) (.var "fc0_92")
      (.vals [ctx.x3Lo] (pointAddUnequalXSubRightRawState ctx)) :=
    Step.var (lowEnv_inputLo ctx)
  have hrightHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalXSubRightLowEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) (.var "fc0_91")
      (.vals [pointAddUnequalXSubRightHi ctx]
        (pointAddUnequalXSubRightRawState ctx)) :=
    Step.var (lowEnv_rightHi ctx)
  have hrightLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalXSubRightLowEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) (.var "fc0_90")
      (.vals [pointAddUnequalXSubRightLo ctx]
        (pointAddUnequalXSubRightRawState ctx)) :=
    Step.var (lowEnv_rightLo ctx)
  have hborrow : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalXSubRightLowEnv ctx)
      (pointAddUnequalXSubRightRawState ctx)
      (.builtin .gt [.var "fc0_90", .var "fc0_92"])
      (.vals [b2w (BitVec.ult ctx.x3Lo (pointAddUnequalXSubRightLo ctx))]
        (pointAddUnequalXSubRightRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hinputLo) hrightLo) rfl
  have hinner : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalXSubRightLowEnv ctx)
      (pointAddUnequalXSubRightRawState ctx)
      (.builtin .sub [.var "fc0_93", .var "fc0_91"])
      (.vals [ctx.x3Hi - pointAddUnequalXSubRightHi ctx]
        (pointAddUnequalXSubRightRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hrightHi) hinputHi) rfl
  have hfinal : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalXSubRightLowEnv ctx)
      (pointAddUnequalXSubRightRawState ctx)
      (.builtin .sub
        [.builtin .sub [.var "fc0_93", .var "fc0_91"],
         .builtin .gt [.var "fc0_90", .var "fc0_92"]])
      (.vals [ctx.x3Hi - pointAddUnequalXSubRightHi ctx -
          b2w (BitVec.ult ctx.x3Lo (pointAddUnequalXSubRightLo ctx))]
        (pointAddUnequalXSubRightRawState ctx)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hborrow) hinner) rfl
  simpa only [pointAddUnequalXSubRightRaw, pointAddUnequalXSubRightRawHi]
    using hfinal

theorem step_pointAddUnequalXSubRightHighGeneric
    (ctx : PointAddUnequalXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalXSubRightLowEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) pointAddUnequalXSubRightRawStmt5
      (pointAddUnequalXSubRightHighEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) .normal := by
  rw [pointAddUnequalXSubRightRawStmt5_eq]
  exact Step.assignVal (step_pointAddUnequalXSubRightHighExprGeneric ctx) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
