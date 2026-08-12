import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleYSubOutputs

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleYSubEnv (ctx : PointAddDoubleYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore ctx.env (pointAddDoubleYSubWorkEnv ctx)

theorem step_pointAddDoubleYSubBodyGeneric (ctx : PointAddDoubleYSubContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) ctx.env ctx.state pointAddDoubleYSubBody
      (pointAddDoubleYSubWorkEnv ctx) (pointAddDoubleYSubRawState ctx) .normal := by
  rw [pointAddDoubleYSubBody_eq]
  exact Step.seqCons (step_pointAddDoubleYSubRawDeclGeneric ctx)
    (Step.seqCons (step_pointAddDoubleYSubRawBlockGeneric ctx)
      (Step.seqCons (step_pointAddDoubleYSubRepairGeneric ctx)
        (step_pointAddDoubleYSubOutputsGeneric ctx)))

theorem step_pointAddDoubleYSubGeneric (ctx : PointAddDoubleYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      ctx.env ctx.state pointAddDoubleYSubStmt (pointAddDoubleYSubEnv ctx)
      (pointAddDoubleYSubRawState ctx) .normal := by
  rw [pointAddDoubleYSubStmt_eq, pointAddDoubleYSubEnv]
  apply Step.block
  rw [hoist_pointAddDoubleYSubBody]
  exact step_pointAddDoubleYSubBodyGeneric ctx

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
