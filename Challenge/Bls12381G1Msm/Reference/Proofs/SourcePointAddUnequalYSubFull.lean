import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalYSubOutputs

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalYSubEnv (ctx : PointAddUnequalYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore ctx.env (pointAddUnequalYSubWorkEnv ctx)

theorem step_pointAddUnequalYSubBodyGeneric (ctx : PointAddUnequalYSubContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) ctx.env ctx.state pointAddUnequalYSubBody
      (pointAddUnequalYSubWorkEnv ctx) (pointAddUnequalYSubRawState ctx) .normal := by
  rw [pointAddUnequalYSubBody_eq]
  exact Step.seqCons (step_pointAddUnequalYSubRawDeclGeneric ctx)
    (Step.seqCons (step_pointAddUnequalYSubRawBlockGeneric ctx)
      (Step.seqCons (step_pointAddUnequalYSubRepairGeneric ctx)
        (step_pointAddUnequalYSubOutputsGeneric ctx)))

theorem step_pointAddUnequalYSubGeneric (ctx : PointAddUnequalYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      ctx.env ctx.state pointAddUnequalYSubStmt (pointAddUnequalYSubEnv ctx)
      (pointAddUnequalYSubRawState ctx) .normal := by
  rw [pointAddUnequalYSubStmt_eq, pointAddUnequalYSubEnv]
  apply Step.block
  rw [hoist_pointAddUnequalYSubBody]
  exact step_pointAddUnequalYSubBodyGeneric ctx

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
