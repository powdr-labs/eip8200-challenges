import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalInvOutput
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Sequence-only composition of the inlined unequal inversion body. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem soundStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt Challenge.EvmProof.modexpExec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect funs V st stmt
      V' st' outcome :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.1
    _ _ _ _ _ _ _ h

private theorem soundStmts {n funs V st stmts V' st' outcome}
    (h : Interp.execStmts Challenge.EvmProof.modexpExec n funs V st stmts =
      .ok (V', st', outcome)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st stmts
      V' st' outcome :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.2.1
    _ _ _ _ _ _ _ h

private theorem appendNormal {funs V st xs Vmid stmid ys Vend stend o}
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

theorem step_pointAddUnequalInvBody (yst : EvmState)
    (out left right : U256)
    (hhi : (pointAddUnequalDenominatorResult yst out left right).1.toNat <
      2 ^ 128) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddUnequalInvInitialEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right)
      pointAddUnequalInvBody
      (pointAddUnequalInvFinalWorkEnv yst out left right)
      (pointAddUnequalInvFinalState yst out left right) .normal := by
  have hcall := soundStmt
    (exec_pointAddUnequalInvCall yst out left right hhi)
  have houtput := soundStmts
    (exec_pointAddUnequalInvOutput yst out left right)
  rw [pointAddUnequalInvBody_eq]
  exact appendNormal (step_pointAddUnequalInvPrefix yst out left right)
    (Step.seqCons hcall houtput)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
