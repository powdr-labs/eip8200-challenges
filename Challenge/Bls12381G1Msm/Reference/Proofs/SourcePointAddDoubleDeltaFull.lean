import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleDeltaOutputs

set_option warningAsError true

/-! Complete generic `left.x - x3` block, behind the normalized boundary. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleDeltaEnv (ctx : PointAddDoubleDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore ctx.env (pointAddDoubleDeltaWorkEnv ctx)

theorem step_pointAddDoubleDeltaBodyGeneric
    (ctx : PointAddDoubleDeltaContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) ctx.env ctx.state pointAddDoubleDeltaBody
      (pointAddDoubleDeltaWorkEnv ctx)
      (pointAddDoubleDeltaRawState ctx) .normal := by
  rw [pointAddDoubleDeltaBody_eq]
  exact Step.seqCons (step_pointAddDoubleDeltaRawDeclGeneric ctx)
    (Step.seqCons (step_pointAddDoubleDeltaRawBlockGeneric ctx)
      (Step.seqCons (step_pointAddDoubleDeltaRepairGeneric ctx)
        (step_pointAddDoubleDeltaOutputsGeneric ctx)))

theorem step_pointAddDoubleDeltaGeneric
    (ctx : PointAddDoubleDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns ctx.env ctx.state pointAddDoubleDeltaStmt
      (pointAddDoubleDeltaEnv ctx)
      (pointAddDoubleDeltaRawState ctx) .normal := by
  rw [pointAddDoubleDeltaStmt_eq, pointAddDoubleDeltaEnv]
  apply Step.block
  rw [hoist_pointAddDoubleDeltaBody]
  exact step_pointAddDoubleDeltaBodyGeneric ctx

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
