import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalPostludeStore

set_option warningAsError true

/-! Four individually relational output stores in the unequal-point postlude. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem postEnv2_xHi (ctx : PointAddUnequalPostContext) :
    VEnv.get (pointAddUnequalPostEnv2 ctx) "\x00136" = some ctx.xHi := by
  rw [pointAddUnequalPostEnv2, venv_get_set_ne _ _ _ _ (by decide),
    pointAddUnequalPostEnv1, venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_xHi

private theorem postEnv2_x125 (ctx : PointAddUnequalPostContext) :
    VEnv.get (pointAddUnequalPostEnv2 ctx) "\x00139" = some ctx.xHi := by
  rw [pointAddUnequalPostEnv2]
  apply venv_get_set_self_of_some
  rw [pointAddUnequalPostEnv1, venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_tempLo

private theorem postEnv2_x124 (ctx : PointAddUnequalPostContext) :
    VEnv.get (pointAddUnequalPostEnv2 ctx) "\x00138" = some ctx.xLo := by
  rw [pointAddUnequalPostEnv2, venv_get_set_ne _ _ _ _ (by decide),
    pointAddUnequalPostEnv1]
  apply venv_get_set_self_of_some
  exact ctx.env_tempHi

private theorem postEnv_out (ctx : PointAddUnequalPostContext) :
    VEnv.get (pointAddUnequalPostEnv ctx) "\x00136" =
      some (pointAddUnequalPostOut ctx) := by
  rw [pointAddUnequalPostEnv]
  apply venv_get_set_self_of_some
  exact postEnv2_xHi ctx

private theorem postEnv_xHi (ctx : PointAddUnequalPostContext) :
    VEnv.get (pointAddUnequalPostEnv ctx) "\x00139" = some ctx.xHi := by
  rw [pointAddUnequalPostEnv, venv_get_set_ne _ _ _ _ (by decide)]
  exact postEnv2_x125 ctx

private theorem postEnv_xLo (ctx : PointAddUnequalPostContext) :
    VEnv.get (pointAddUnequalPostEnv ctx) "\x00138" = some ctx.xLo := by
  rw [pointAddUnequalPostEnv, venv_get_set_ne _ _ _ _ (by decide)]
  exact postEnv2_x124 ctx

private theorem postEnv_yHi (ctx : PointAddUnequalPostContext) :
    VEnv.get (pointAddUnequalPostEnv ctx) "\x00140" = some ctx.yHi := by
  rw [pointAddUnequalPostEnv, venv_get_set_ne _ _ _ _ (by decide),
    pointAddUnequalPostEnv2, venv_get_set_ne _ _ _ _ (by decide),
    pointAddUnequalPostEnv1, venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_yHi

private theorem postEnv_yLo (ctx : PointAddUnequalPostContext) :
    VEnv.get (pointAddUnequalPostEnv ctx) "\x00141" = some ctx.yLo := by
  rw [pointAddUnequalPostEnv, venv_get_set_ne _ _ _ _ (by decide),
    pointAddUnequalPostEnv2, venv_get_set_ne _ _ _ _ (by decide),
    pointAddUnequalPostEnv1, venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_yLo

theorem step_pointAddUnequalPostStmt4Generic (ctx : PointAddUnequalPostContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalPostEnv ctx) (pointAddUnequalPostLoadState ctx)
      pointAddUnequalPostStmt4 (pointAddUnequalPostEnv ctx)
      (pointAddUnequalPostState1 ctx) .normal := by
  rw [pointAddUnequalPostStmt4_eq, pointAddUnequalPostState1]
  exact step_pointAddUnequal_mstoreVars (postEnv_out ctx) (postEnv_xHi ctx)

theorem step_pointAddUnequalPostStmt5Generic (ctx : PointAddUnequalPostContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalPostEnv ctx) (pointAddUnequalPostState1 ctx)
      pointAddUnequalPostStmt5 (pointAddUnequalPostEnv ctx)
      (pointAddUnequalPostState2 ctx) .normal := by
  rw [pointAddUnequalPostStmt5_eq, pointAddUnequalPostState2]
  exact step_pointAddUnequal_mstoreAddVar 32 (postEnv_out ctx) (postEnv_xLo ctx)

theorem step_pointAddUnequalPostStmt6Generic (ctx : PointAddUnequalPostContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalPostEnv ctx) (pointAddUnequalPostState2 ctx)
      pointAddUnequalPostStmt6 (pointAddUnequalPostEnv ctx)
      (pointAddUnequalPostState3 ctx) .normal := by
  rw [pointAddUnequalPostStmt6_eq, pointAddUnequalPostState3]
  exact step_pointAddUnequal_mstoreAddVar 64 (postEnv_out ctx) (postEnv_yHi ctx)

theorem step_pointAddUnequalPostStmt7Generic (ctx : PointAddUnequalPostContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalPostEnv ctx) (pointAddUnequalPostState3 ctx)
      pointAddUnequalPostStmt7 (pointAddUnequalPostEnv ctx)
      (pointAddUnequalPostState ctx) .normal := by
  rw [pointAddUnequalPostStmt7_eq, pointAddUnequalPostState]
  exact step_pointAddUnequal_mstoreAddVar 96 (postEnv_out ctx) (postEnv_yLo ctx)

theorem step_pointAddUnequalPostStoresGeneric (ctx : PointAddUnequalPostContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalPostEnv ctx) (pointAddUnequalPostLoadState ctx)
      (pointAddUnequalPostlude.drop 4) (pointAddUnequalPostEnv ctx)
      (pointAddUnequalPostState ctx) .normal := by
  rw [show pointAddUnequalPostlude.drop 4 =
    [pointAddUnequalPostStmt4, pointAddUnequalPostStmt5,
     pointAddUnequalPostStmt6, pointAddUnequalPostStmt7] by rfl]
  exact Step.seqCons (step_pointAddUnequalPostStmt4Generic ctx)
    (Step.seqCons (step_pointAddUnequalPostStmt5Generic ctx)
      (Step.seqCons (step_pointAddUnequalPostStmt6Generic ctx)
        (Step.seqCons (step_pointAddUnequalPostStmt7Generic ctx) Step.seqNil)))

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
