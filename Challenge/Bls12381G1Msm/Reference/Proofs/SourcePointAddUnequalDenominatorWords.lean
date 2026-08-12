import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDenominatorRightHi

set_option warningAsError true

/-! Value-only raw-word boundary for the unequal denominator. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem venv_setMany_singleton (V : VEnv D) (x : Ident)
    (v : D.Value) : VEnv.setMany V [x] [v] = VEnv.set V x v := by
  rfl

structure PointAddUnequalDenominatorContext where
  env : VEnv Challenge.EvmProof.modexpExec.toDialect
  state : EvmState
  leftHi : U256
  leftLo : U256
  rightHi : U256
  rightLo : U256
  env_leftHi : VEnv.get env "fc0_77" = some leftHi
  env_leftLo : VEnv.get env "fc0_76" = some leftLo
  env_rightHi : VEnv.get env "fc0_79" = some rightHi
  env_rightLo : VEnv.get env "fc0_78" = some rightLo

def pointAddUnequalDenominatorRawGeneric
    (ctx : PointAddUnequalDenominatorContext) : U256 × U256 :=
  (ctx.rightHi - ctx.leftHi - b2w (BitVec.ult ctx.rightLo ctx.leftLo),
    ctx.rightLo - ctx.leftLo)

def pointAddUnequalDenominatorLowEnvGeneric
    (ctx : PointAddUnequalDenominatorContext) :=
  VEnv.setMany ctx.env ["fc0_75"]
    [(pointAddUnequalDenominatorRawGeneric ctx).2]

def pointAddUnequalDenominatorHighEnvGeneric
    (ctx : PointAddUnequalDenominatorContext) :=
  VEnv.setMany (pointAddUnequalDenominatorLowEnvGeneric ctx) ["fc0_74"]
    [(pointAddUnequalDenominatorRawGeneric ctx).1]

theorem step_pointAddUnequalDenominatorLowGeneric
    (ctx : PointAddUnequalDenominatorContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) ctx.env ctx.state
      pointAddUnequalDenominatorRawStmt4
      (pointAddUnequalDenominatorLowEnvGeneric ctx) ctx.state .normal := by
  rw [pointAddUnequalDenominatorRawStmt4_eq]
  have hright : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) ctx.env ctx.state (.var "fc0_76")
      (.vals [ctx.leftLo] ctx.state) := Step.var ctx.env_leftLo
  have hleft : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) ctx.env ctx.state (.var "fc0_78")
      (.vals [ctx.rightLo] ctx.state) := Step.var ctx.env_rightLo
  have hsub : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) ctx.env ctx.state
      (.builtin .sub [.var "fc0_78", .var "fc0_76"])
      (.vals [ctx.rightLo - ctx.leftLo] ctx.state) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hright) hleft) rfl
  simpa [pointAddUnequalDenominatorLowEnvGeneric,
    pointAddUnequalDenominatorRawGeneric, venv_setMany_singleton] using
    (Step.assignVal hsub (by rfl))

private theorem low_leftHi (ctx : PointAddUnequalDenominatorContext) :
    VEnv.get (pointAddUnequalDenominatorLowEnvGeneric ctx) "fc0_77" =
      some ctx.leftHi := by
  rw [pointAddUnequalDenominatorLowEnvGeneric, venv_setMany_singleton,
    venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_leftHi

private theorem low_leftLo (ctx : PointAddUnequalDenominatorContext) :
    VEnv.get (pointAddUnequalDenominatorLowEnvGeneric ctx) "fc0_76" =
      some ctx.leftLo := by
  rw [pointAddUnequalDenominatorLowEnvGeneric, venv_setMany_singleton,
    venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_leftLo

private theorem low_rightHi (ctx : PointAddUnequalDenominatorContext) :
    VEnv.get (pointAddUnequalDenominatorLowEnvGeneric ctx) "fc0_79" =
      some ctx.rightHi := by
  rw [pointAddUnequalDenominatorLowEnvGeneric, venv_setMany_singleton,
    venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_rightHi

private theorem low_rightLo (ctx : PointAddUnequalDenominatorContext) :
    VEnv.get (pointAddUnequalDenominatorLowEnvGeneric ctx) "fc0_78" =
      some ctx.rightLo := by
  rw [pointAddUnequalDenominatorLowEnvGeneric, venv_setMany_singleton,
    venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_rightLo

theorem step_pointAddUnequalDenominatorHighGeneric
    (ctx : PointAddUnequalDenominatorContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorLowEnvGeneric ctx) ctx.state
      pointAddUnequalDenominatorRawStmt5
      (pointAddUnequalDenominatorHighEnvGeneric ctx) ctx.state .normal := by
  rw [pointAddUnequalDenominatorRawStmt5_eq]
  have hleftLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorLowEnvGeneric ctx) ctx.state (.var "fc0_76")
      (.vals [ctx.leftLo] ctx.state) := Step.var (low_leftLo ctx)
  have hleftHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorLowEnvGeneric ctx) ctx.state (.var "fc0_77")
      (.vals [ctx.leftHi] ctx.state) := Step.var (low_leftHi ctx)
  have hrightLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorLowEnvGeneric ctx) ctx.state (.var "fc0_78")
      (.vals [ctx.rightLo] ctx.state) := Step.var (low_rightLo ctx)
  have hrightHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorLowEnvGeneric ctx) ctx.state (.var "fc0_79")
      (.vals [ctx.rightHi] ctx.state) := Step.var (low_rightHi ctx)
  have hborrow : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorLowEnvGeneric ctx) ctx.state
      (.builtin .gt [.var "fc0_76", .var "fc0_78"])
      (.vals [b2w (BitVec.ult ctx.rightLo ctx.leftLo)] ctx.state) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hrightLo) hleftLo) rfl
  have hinner : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorLowEnvGeneric ctx) ctx.state
      (.builtin .sub [.var "fc0_79", .var "fc0_77"])
      (.vals [ctx.rightHi - ctx.leftHi] ctx.state) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hleftHi) hrightHi) rfl
  have hfinal : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorLowEnvGeneric ctx) ctx.state
      (.builtin .sub
        [.builtin .sub [.var "fc0_79", .var "fc0_77"],
         .builtin .gt [.var "fc0_76", .var "fc0_78"]])
      (.vals [ctx.rightHi - ctx.leftHi -
        b2w (BitVec.ult ctx.rightLo ctx.leftLo)] ctx.state) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hborrow) hinner) rfl
  simpa [pointAddUnequalDenominatorHighEnvGeneric,
    pointAddUnequalDenominatorRawGeneric, venv_setMany_singleton] using
    (Step.assignVal hfinal (by rfl))

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
