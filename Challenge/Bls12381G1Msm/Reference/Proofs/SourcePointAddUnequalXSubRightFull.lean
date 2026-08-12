import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubRightOutputs

set_option warningAsError true

/-! Complete generic second unequal-point x subtraction, before the concrete bridge. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem step_pointAddUnequalRight_appendNormal
    {funs V st xs Vmid stmid ys Vend stend o}
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

theorem step_pointAddUnequalXSubRightGeneric
    (ctx : PointAddUnequalXSubRightContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) ctx.env ctx.state pointAddUnequalXSubRightTail
      (pointAddUnequalXSubRightWorkEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) .normal := by
  rw [show pointAddUnequalXSubRightTail =
      pointAddUnequalXSubRightTail.take 2 ++
        [pointAddUnequalXSubRightRepairStmt,
         pointAddUnequalXSubRightOutHiStmt,
         pointAddUnequalXSubRightOutLoStmt] by rfl]
  exact step_pointAddUnequalRight_appendNormal
    (step_pointAddUnequalXSubRightRawGeneric ctx)
    (Step.seqCons (step_pointAddUnequalXSubRightRepairGeneric ctx)
      (step_pointAddUnequalXSubRightOutputsGeneric ctx))

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
