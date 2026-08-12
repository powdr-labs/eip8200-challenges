import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubLeftSelected
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Composition of the raw prefix and selected repair statement. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleXSubLeftPrefixRepair : Block Op :=
  pointAddDoubleXSubLeftBody.take 2 ++ [pointAddDoubleXSubLeftRepairStmt]

private theorem soundStmts {n funs V st stmts V' st' outcome}
    (h : Interp.execStmts Challenge.EvmProof.modexpExec n funs V st stmts =
      .ok (V', st', outcome)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st stmts
      V' st' outcome :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.2.1
    _ _ _ _ _ _ _ h

theorem step_appendNormal {funs V st xs Vmid stmid ys Vend stend o}
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

theorem step_pointAddDoubleXSubLeftPrefixRepair (yst : EvmState)
    (out left right : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect ([] :: pointAddBodyFuns)
      (pointAddDoubleX3Env yst out left right)
      (pointAddDoubleX3State yst out left right)
      pointAddDoubleXSubLeftPrefixRepair
      (pointAddDoubleXSubLeftSelectedEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right) .normal := by
  exact step_appendNormal
    (soundStmts (exec_pointAddDoubleXSubLeftRaw yst out left right))
    (Step.seqCons
      (step_pointAddDoubleXSubLeftRepairSelected yst out left right) Step.seqNil)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
