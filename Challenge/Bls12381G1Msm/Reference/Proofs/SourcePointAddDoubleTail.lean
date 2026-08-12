import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleYSubEnvLookup
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoublePostludeFull

set_option warningAsError true

/-! Normalized existential firebreak for the final y subtraction and stores. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

structure PointAddDoubleYSubPostContext where
  ysub : PointAddDoubleYSubContext
  xHi : U256
  xLo : U256
  tempHi : U256
  tempLo : U256
  env_xHi : VEnv.get ysub.env "\x00122" = some xHi
  env_xLo : VEnv.get ysub.env "\x00123" = some xLo
  env_tempHi : VEnv.get ysub.env "\x00124" = some tempHi
  env_tempLo : VEnv.get ysub.env "\x00125" = some tempLo

private theorem ysubEnv_xHi (ctx : PointAddDoubleYSubPostContext) :
    VEnv.get (pointAddDoubleYSubEnv ctx.ysub) "\x00122" = some ctx.xHi := by
  rw [pointAddDoubleYSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_xHi
private theorem ysubEnv_xLo (ctx : PointAddDoubleYSubPostContext) :
    VEnv.get (pointAddDoubleYSubEnv ctx.ysub) "\x00123" = some ctx.xLo := by
  rw [pointAddDoubleYSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_xLo
private theorem ysubEnv_yHi (ctx : PointAddDoubleYSubPostContext) :
    VEnv.get (pointAddDoubleYSubEnv ctx.ysub) "\x00126" =
      some (pointAddDoubleYSubResult ctx.ysub).1 := by
  rw [pointAddDoubleYSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  apply venv_get_set_self_of_some
  exact ctx.ysub.env_hi
private theorem ysubEnv_yLo (ctx : PointAddDoubleYSubPostContext) :
    VEnv.get (pointAddDoubleYSubEnv ctx.ysub) "\x00127" =
      some (pointAddDoubleYSubResult ctx.ysub).2 := by
  rw [pointAddDoubleYSubEnv_eq]
  apply venv_get_set_self_of_some
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.ysub.env_lo
private theorem ysubEnv_tempHi (ctx : PointAddDoubleYSubPostContext) :
    VEnv.get (pointAddDoubleYSubEnv ctx.ysub) "\x00124" =
      some ctx.tempHi := by
  rw [pointAddDoubleYSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_tempHi
private theorem ysubEnv_tempLo (ctx : PointAddDoubleYSubPostContext) :
    VEnv.get (pointAddDoubleYSubEnv ctx.ysub) "\x00125" =
      some ctx.tempLo := by
  rw [pointAddDoubleYSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_tempLo

def pointAddDoublePostContextOfYSub (ctx : PointAddDoubleYSubPostContext) :
    PointAddDoublePostContext where
  env := pointAddDoubleYSubEnv ctx.ysub
  state := pointAddDoubleYSubRawState ctx.ysub
  xHi := ctx.xHi
  xLo := ctx.xLo
  yHi := (pointAddDoubleYSubResult ctx.ysub).1
  yLo := (pointAddDoubleYSubResult ctx.ysub).2
  tempHi := ctx.tempHi
  tempLo := ctx.tempLo
  env_xHi := ysubEnv_xHi ctx
  env_xLo := ysubEnv_xLo ctx
  env_yHi := ysubEnv_yHi ctx
  env_yLo := ysubEnv_yLo ctx
  env_tempHi := ysubEnv_tempHi ctx
  env_tempLo := ysubEnv_tempLo ctx

theorem step_pointAddDoubleYSubPostGeneric (ctx : PointAddDoubleYSubPostContext) :
    ∃ Vend stend,
      ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
        ctx.ysub.env ctx.ysub.state
        (pointAddDoubleYSubStmt :: pointAddDoublePostlude)
        Vend stend .normal := by
  let post := pointAddDoublePostContextOfYSub ctx
  refine ⟨pointAddDoublePostEnv post, pointAddDoublePostState post, ?_⟩
  exact Step.seqCons (step_pointAddDoubleYSubGeneric ctx.ysub)
    (step_pointAddDoublePostludeGeneric post)

def pointAddDoubleYSubPostContext (yst : EvmState) (out left right : U256) :
    PointAddDoubleYSubPostContext where
  ysub := pointAddDoubleYSubContext yst out left right
  xHi := (pointAddDoubleXSubResult yst out left right).1
  xLo := (pointAddDoubleXSubResult yst out left right).2
  tempHi := (pointAddDoubleDeltaResult
    (pointAddDoubleDeltaContext yst out left right)).1
  tempLo := (pointAddDoubleDeltaResult
    (pointAddDoubleDeltaContext yst out left right)).2
  env_xHi := pointAddDoubleYMulEnv_xHi yst out left right
  env_xLo := pointAddDoubleYMulEnv_xLo yst out left right
  env_tempHi := pointAddDoubleYMulEnv_tempHi yst out left right
  env_tempLo := pointAddDoubleYMulEnv_tempLo yst out left right

theorem step_pointAddDoubleTail (yst : EvmState) (out left right : U256) :
    ∃ Vend stend,
      ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
        (pointAddDoubleYMulEnv yst out left right)
        (pointAddDoubleYMulState yst out left right)
        (pointAddDoubleYSubStmt :: pointAddDoublePostlude)
        Vend stend .normal := by
  exact step_pointAddDoubleYSubPostGeneric
    (pointAddDoubleYSubPostContext yst out left right)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
