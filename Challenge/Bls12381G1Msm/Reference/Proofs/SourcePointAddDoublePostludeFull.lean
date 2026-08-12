import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoublePostludeStores

set_option warningAsError true

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

theorem step_pointAddDoublePostludeGeneric (ctx : PointAddDoublePostContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      ctx.env ctx.state pointAddDoublePostlude
      (pointAddDoublePostEnv ctx) (pointAddDoublePostState ctx) .normal := by
  rw [show pointAddDoublePostlude = pointAddDoublePostlude.take 4 ++
      pointAddDoublePostlude.drop 4 by
    exact (List.take_append_drop 4 pointAddDoublePostlude).symm]
  exact step_appendNormal (step_pointAddDoublePostPrefixGeneric ctx)
    (step_pointAddDoublePostStoresGeneric ctx)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
