import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubRightOutputs

set_option warningAsError true

/-! Complete generic second point-double x subtraction, before the concrete bridge. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem step_appendNormal {funs V st xs Vmid stmid ys Vend stend o}
    (hx : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st xs
      Vmid stmid .normal)
    (hy : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs Vmid stmid ys
      Vend stend o) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st (xs ++ ys)
      Vend stend o := by
  induction xs generalizing V st with
  | nil => cases hx; simpa using hy
  | cons head tail ih =>
      cases hx with
      | seqCons hh ht => exact Step.seqCons hh (ih ht)
      | seqStop _ hn => exact False.elim (hn rfl)

theorem step_pointAddDoubleXSubRightGeneric
    (ctx : PointAddDoubleXSubRightContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) ctx.env ctx.state pointAddDoubleXSubRightTail
      (pointAddDoubleXSubRightWorkEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) .normal := by
  rw [show pointAddDoubleXSubRightTail =
      pointAddDoubleXSubRightTail.take 2 ++
        [pointAddDoubleXSubRightRepairStmt,
         pointAddDoubleXSubRightOutHiStmt,
         pointAddDoubleXSubRightOutLoStmt] by rfl]
  exact step_appendNormal (step_pointAddDoubleXSubRightRawGeneric ctx)
    (Step.seqCons (step_pointAddDoubleXSubRightRepairGeneric ctx)
      (step_pointAddDoubleXSubRightOutputsGeneric ctx))

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
