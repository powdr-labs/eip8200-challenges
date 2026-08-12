import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubLeftSelected
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Composition of the raw prefix and selected repair statement. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalXSubLeftPrefixRepair : Block Op :=
  pointAddUnequalXSubLeftBody.take 2 ++ [pointAddUnequalXSubLeftRepairStmt]

private theorem soundStmts {n funs V st stmts V' st' outcome}
    (h : Interp.execStmts Challenge.EvmProof.modexpExec n funs V st stmts =
      .ok (V', st', outcome)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st stmts
      V' st' outcome :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.2.1
    _ _ _ _ _ _ _ h

theorem step_pointAddUnequal_appendNormal
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

theorem step_pointAddUnequalXSubLeftPrefixRepair (yst : EvmState)
    (out left right : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect ([] :: pointAddBodyFuns)
      (pointAddUnequalX3Env yst out left right)
      (pointAddUnequalX3State yst out left right)
      pointAddUnequalXSubLeftPrefixRepair
      (pointAddUnequalXSubLeftSelectedEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right) .normal := by
  exact step_pointAddUnequal_appendNormal
    (soundStmts (exec_pointAddUnequalXSubLeftRaw yst out left right))
    (Step.seqCons
      (step_pointAddUnequalXSubLeftRepairSelected yst out left right) Step.seqNil)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
