import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoublePostludeStore

set_option warningAsError true

/-! Four individually relational output stores in the point-doubling postlude. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem postEnv2_xHi (ctx : PointAddDoublePostContext) :
    VEnv.get (pointAddDoublePostEnv2 ctx) "\x00122" = some ctx.xHi := by
  rw [pointAddDoublePostEnv2, venv_get_set_ne _ _ _ _ (by decide),
    pointAddDoublePostEnv1, venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_xHi

private theorem postEnv2_x125 (ctx : PointAddDoublePostContext) :
    VEnv.get (pointAddDoublePostEnv2 ctx) "\x00125" = some ctx.xHi := by
  rw [pointAddDoublePostEnv2]
  apply venv_get_set_self_of_some
  rw [pointAddDoublePostEnv1, venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_tempLo

private theorem postEnv2_x124 (ctx : PointAddDoublePostContext) :
    VEnv.get (pointAddDoublePostEnv2 ctx) "\x00124" = some ctx.xLo := by
  rw [pointAddDoublePostEnv2, venv_get_set_ne _ _ _ _ (by decide),
    pointAddDoublePostEnv1]
  apply venv_get_set_self_of_some
  exact ctx.env_tempHi

private theorem postEnv_out (ctx : PointAddDoublePostContext) :
    VEnv.get (pointAddDoublePostEnv ctx) "\x00122" =
      some (pointAddDoublePostOut ctx) := by
  rw [pointAddDoublePostEnv]
  apply venv_get_set_self_of_some
  exact postEnv2_xHi ctx

private theorem postEnv_xHi (ctx : PointAddDoublePostContext) :
    VEnv.get (pointAddDoublePostEnv ctx) "\x00125" = some ctx.xHi := by
  rw [pointAddDoublePostEnv, venv_get_set_ne _ _ _ _ (by decide)]
  exact postEnv2_x125 ctx

private theorem postEnv_xLo (ctx : PointAddDoublePostContext) :
    VEnv.get (pointAddDoublePostEnv ctx) "\x00124" = some ctx.xLo := by
  rw [pointAddDoublePostEnv, venv_get_set_ne _ _ _ _ (by decide)]
  exact postEnv2_x124 ctx

private theorem postEnv_yHi (ctx : PointAddDoublePostContext) :
    VEnv.get (pointAddDoublePostEnv ctx) "\x00126" = some ctx.yHi := by
  rw [pointAddDoublePostEnv, venv_get_set_ne _ _ _ _ (by decide),
    pointAddDoublePostEnv2, venv_get_set_ne _ _ _ _ (by decide),
    pointAddDoublePostEnv1, venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_yHi

private theorem postEnv_yLo (ctx : PointAddDoublePostContext) :
    VEnv.get (pointAddDoublePostEnv ctx) "\x00127" = some ctx.yLo := by
  rw [pointAddDoublePostEnv, venv_get_set_ne _ _ _ _ (by decide),
    pointAddDoublePostEnv2, venv_get_set_ne _ _ _ _ (by decide),
    pointAddDoublePostEnv1, venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_yLo

theorem step_pointAddDoublePostStmt4Generic (ctx : PointAddDoublePostContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoublePostEnv ctx) (pointAddDoublePostLoadState ctx)
      pointAddDoublePostStmt4 (pointAddDoublePostEnv ctx)
      (pointAddDoublePostState1 ctx) .normal := by
  rw [pointAddDoublePostStmt4_eq, pointAddDoublePostState1]
  exact step_mstoreVars (postEnv_out ctx) (postEnv_xHi ctx)

theorem step_pointAddDoublePostStmt5Generic (ctx : PointAddDoublePostContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoublePostEnv ctx) (pointAddDoublePostState1 ctx)
      pointAddDoublePostStmt5 (pointAddDoublePostEnv ctx)
      (pointAddDoublePostState2 ctx) .normal := by
  rw [pointAddDoublePostStmt5_eq, pointAddDoublePostState2]
  exact step_mstoreAddVar 32 (postEnv_out ctx) (postEnv_xLo ctx)

theorem step_pointAddDoublePostStmt6Generic (ctx : PointAddDoublePostContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoublePostEnv ctx) (pointAddDoublePostState2 ctx)
      pointAddDoublePostStmt6 (pointAddDoublePostEnv ctx)
      (pointAddDoublePostState3 ctx) .normal := by
  rw [pointAddDoublePostStmt6_eq, pointAddDoublePostState3]
  exact step_mstoreAddVar 64 (postEnv_out ctx) (postEnv_yHi ctx)

theorem step_pointAddDoublePostStmt7Generic (ctx : PointAddDoublePostContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoublePostEnv ctx) (pointAddDoublePostState3 ctx)
      pointAddDoublePostStmt7 (pointAddDoublePostEnv ctx)
      (pointAddDoublePostState ctx) .normal := by
  rw [pointAddDoublePostStmt7_eq, pointAddDoublePostState]
  exact step_mstoreAddVar 96 (postEnv_out ctx) (postEnv_yLo ctx)

theorem step_pointAddDoublePostStoresGeneric (ctx : PointAddDoublePostContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoublePostEnv ctx) (pointAddDoublePostLoadState ctx)
      (pointAddDoublePostlude.drop 4) (pointAddDoublePostEnv ctx)
      (pointAddDoublePostState ctx) .normal := by
  rw [show pointAddDoublePostlude.drop 4 =
    [pointAddDoublePostStmt4, pointAddDoublePostStmt5,
     pointAddDoublePostStmt6, pointAddDoublePostStmt7] by rfl]
  exact Step.seqCons (step_pointAddDoublePostStmt4Generic ctx)
    (Step.seqCons (step_pointAddDoublePostStmt5Generic ctx)
      (Step.seqCons (step_pointAddDoublePostStmt6Generic ctx)
        (Step.seqCons (step_pointAddDoublePostStmt7Generic ctx) Step.seqNil)))

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
