import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalPostludeStores

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem step_pointAddUnequalPost_appendNormal
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

theorem step_pointAddUnequalPostludeGeneric (ctx : PointAddUnequalPostContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      ctx.env ctx.state pointAddUnequalPostlude
      (pointAddUnequalPostEnv ctx) (pointAddUnequalPostState ctx) .normal := by
  rw [show pointAddUnequalPostlude = pointAddUnequalPostlude.take 4 ++
      pointAddUnequalPostlude.drop 4 by
    exact (List.take_append_drop 4 pointAddUnequalPostlude).symm]
  exact step_pointAddUnequalPost_appendNormal
    (step_pointAddUnequalPostPrefixGeneric ctx)
    (step_pointAddUnequalPostStoresGeneric ctx)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
