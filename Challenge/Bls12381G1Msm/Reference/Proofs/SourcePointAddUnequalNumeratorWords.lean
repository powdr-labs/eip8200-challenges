import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalNumeratorRightHi

set_option warningAsError true

/-! Value-only raw-word boundary for the unequal numerator. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem venv_setMany_singleton (V : VEnv D) (x : Ident)
    (v : D.Value) : VEnv.setMany V [x] [v] = VEnv.set V x v := by
  rfl

structure PointAddUnequalNumeratorContext where
  env : VEnv Challenge.EvmProof.modexpExec.toDialect
  state : EvmState
  leftHi : U256
  leftLo : U256
  rightHi : U256
  rightLo : U256
  env_leftHi : VEnv.get env "fc0_70" = some leftHi
  env_leftLo : VEnv.get env "fc0_69" = some leftLo
  env_rightHi : VEnv.get env "fc0_72" = some rightHi
  env_rightLo : VEnv.get env "fc0_71" = some rightLo

def pointAddUnequalNumeratorRawGeneric
    (ctx : PointAddUnequalNumeratorContext) : U256 × U256 :=
  (ctx.rightHi - ctx.leftHi - b2w (BitVec.ult ctx.rightLo ctx.leftLo),
    ctx.rightLo - ctx.leftLo)

def pointAddUnequalNumeratorLowEnvGeneric
    (ctx : PointAddUnequalNumeratorContext) :=
  VEnv.setMany ctx.env ["fc0_68"]
    [(pointAddUnequalNumeratorRawGeneric ctx).2]

def pointAddUnequalNumeratorHighEnvGeneric
    (ctx : PointAddUnequalNumeratorContext) :=
  VEnv.setMany (pointAddUnequalNumeratorLowEnvGeneric ctx) ["fc0_67"]
    [(pointAddUnequalNumeratorRawGeneric ctx).1]

theorem step_pointAddUnequalNumeratorLowGeneric
    (ctx : PointAddUnequalNumeratorContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) ctx.env ctx.state
      pointAddUnequalNumeratorRawStmt4
      (pointAddUnequalNumeratorLowEnvGeneric ctx) ctx.state .normal := by
  rw [pointAddUnequalNumeratorRawStmt4_eq]
  have hright : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) ctx.env ctx.state (.var "fc0_69")
      (.vals [ctx.leftLo] ctx.state) := Step.var ctx.env_leftLo
  have hleft : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) ctx.env ctx.state (.var "fc0_71")
      (.vals [ctx.rightLo] ctx.state) := Step.var ctx.env_rightLo
  have hsub : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) ctx.env ctx.state
      (.builtin .sub [.var "fc0_71", .var "fc0_69"])
      (.vals [ctx.rightLo - ctx.leftLo] ctx.state) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hright) hleft) rfl
  simpa [pointAddUnequalNumeratorLowEnvGeneric,
    pointAddUnequalNumeratorRawGeneric, venv_setMany_singleton] using
    (Step.assignVal hsub (by rfl))

private theorem low_leftHi (ctx : PointAddUnequalNumeratorContext) :
    VEnv.get (pointAddUnequalNumeratorLowEnvGeneric ctx) "fc0_70" =
      some ctx.leftHi := by
  rw [pointAddUnequalNumeratorLowEnvGeneric, venv_setMany_singleton,
    venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_leftHi

private theorem low_leftLo (ctx : PointAddUnequalNumeratorContext) :
    VEnv.get (pointAddUnequalNumeratorLowEnvGeneric ctx) "fc0_69" =
      some ctx.leftLo := by
  rw [pointAddUnequalNumeratorLowEnvGeneric, venv_setMany_singleton,
    venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_leftLo

private theorem low_rightHi (ctx : PointAddUnequalNumeratorContext) :
    VEnv.get (pointAddUnequalNumeratorLowEnvGeneric ctx) "fc0_72" =
      some ctx.rightHi := by
  rw [pointAddUnequalNumeratorLowEnvGeneric, venv_setMany_singleton,
    venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_rightHi

private theorem low_rightLo (ctx : PointAddUnequalNumeratorContext) :
    VEnv.get (pointAddUnequalNumeratorLowEnvGeneric ctx) "fc0_71" =
      some ctx.rightLo := by
  rw [pointAddUnequalNumeratorLowEnvGeneric, venv_setMany_singleton,
    venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_rightLo

theorem step_pointAddUnequalNumeratorHighGeneric
    (ctx : PointAddUnequalNumeratorContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorLowEnvGeneric ctx) ctx.state
      pointAddUnequalNumeratorRawStmt5
      (pointAddUnequalNumeratorHighEnvGeneric ctx) ctx.state .normal := by
  rw [pointAddUnequalNumeratorRawStmt5_eq]
  have hleftLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorLowEnvGeneric ctx) ctx.state (.var "fc0_69")
      (.vals [ctx.leftLo] ctx.state) := Step.var (low_leftLo ctx)
  have hleftHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorLowEnvGeneric ctx) ctx.state (.var "fc0_70")
      (.vals [ctx.leftHi] ctx.state) := Step.var (low_leftHi ctx)
  have hrightLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorLowEnvGeneric ctx) ctx.state (.var "fc0_71")
      (.vals [ctx.rightLo] ctx.state) := Step.var (low_rightLo ctx)
  have hrightHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorLowEnvGeneric ctx) ctx.state (.var "fc0_72")
      (.vals [ctx.rightHi] ctx.state) := Step.var (low_rightHi ctx)
  have hborrow : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorLowEnvGeneric ctx) ctx.state
      (.builtin .gt [.var "fc0_69", .var "fc0_71"])
      (.vals [b2w (BitVec.ult ctx.rightLo ctx.leftLo)] ctx.state) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hrightLo) hleftLo) rfl
  have hinner : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorLowEnvGeneric ctx) ctx.state
      (.builtin .sub [.var "fc0_72", .var "fc0_70"])
      (.vals [ctx.rightHi - ctx.leftHi] ctx.state) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hleftHi) hrightHi) rfl
  have hfinal : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorLowEnvGeneric ctx) ctx.state
      (.builtin .sub
        [.builtin .sub [.var "fc0_72", .var "fc0_70"],
         .builtin .gt [.var "fc0_69", .var "fc0_71"]])
      (.vals [ctx.rightHi - ctx.leftHi -
        b2w (BitVec.ult ctx.rightLo ctx.leftLo)] ctx.state) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hborrow) hinner) rfl
  simpa [pointAddUnequalNumeratorHighEnvGeneric,
    pointAddUnequalNumeratorRawGeneric, venv_setMany_singleton] using
    (Step.assignVal hfinal (by rfl))

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
