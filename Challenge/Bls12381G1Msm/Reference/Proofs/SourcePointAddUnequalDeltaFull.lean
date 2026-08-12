import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDeltaOutputs

set_option warningAsError true

/-! Complete generic `left.x - x3` block, behind the normalized boundary. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalDeltaEnv (ctx : PointAddUnequalDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore ctx.env (pointAddUnequalDeltaWorkEnv ctx)

theorem step_pointAddUnequalDeltaBodyGeneric
    (ctx : PointAddUnequalDeltaContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) ctx.env ctx.state pointAddUnequalDeltaBody
      (pointAddUnequalDeltaWorkEnv ctx)
      (pointAddUnequalDeltaRawState ctx) .normal := by
  rw [pointAddUnequalDeltaBody_eq]
  exact Step.seqCons (step_pointAddUnequalDeltaRawDeclGeneric ctx)
    (Step.seqCons (step_pointAddUnequalDeltaRawBlockGeneric ctx)
      (Step.seqCons (step_pointAddUnequalDeltaRepairGeneric ctx)
        (step_pointAddUnequalDeltaOutputsGeneric ctx)))

theorem step_pointAddUnequalDeltaGeneric
    (ctx : PointAddUnequalDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns ctx.env ctx.state pointAddUnequalDeltaStmt
      (pointAddUnequalDeltaEnv ctx)
      (pointAddUnequalDeltaRawState ctx) .normal := by
  rw [pointAddUnequalDeltaStmt_eq, pointAddUnequalDeltaEnv]
  apply Step.block
  rw [hoist_pointAddUnequalDeltaBody]
  exact step_pointAddUnequalDeltaBodyGeneric ctx

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
