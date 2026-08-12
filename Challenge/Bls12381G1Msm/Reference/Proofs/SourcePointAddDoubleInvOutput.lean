import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleInvCall
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Output loads and relational composition of the inlined point-double inversion. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleInvResult (yst : EvmState) (out left right : U256) :
    U256 × U256 :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvResult
    (pointAddDoubleDenArgsState yst out left right)
    (pointAddDoubleDenResult yst out left right).1
    (pointAddDoubleDenResult yst out left right).2

def pointAddDoubleInvFinalState (yst : EvmState) (out left right : U256) : EvmState :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvFinalState
    (pointAddDoubleDenArgsState yst out left right)
    (pointAddDoubleDenResult yst out left right).1
    (pointAddDoubleDenResult yst out left right).2

def pointAddDoubleInvOutputEnv (yst : EvmState) (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (pointAddDoubleInvInitialEnv yst out left right)
    ["\x00118", "\x00119"]
    [(pointAddDoubleInvResult yst out left right).1,
      (pointAddDoubleInvResult yst out left right).2]

private def pointAddDoubleInvFinalWorkEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany
    (VEnv.setMany
      (VEnv.setMany
        (VEnv.setMany (pointAddDoubleInvWorkEnv yst out left right)
          ["fc2_1"] [(pointAddDoubleInvResult yst out left right).1])
        ["fc2_2"] [(pointAddDoubleInvResult yst out left right).2])
      ["\x00118"] [(pointAddDoubleInvResult yst out left right).1])
    ["\x00119"] [(pointAddDoubleInvResult yst out left right).2]

private theorem exec_pointAddDoubleInvOutput (yst : EvmState)
    (out left right : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 70
      ([] :: pointAddBodyFuns)
      (pointAddDoubleInvWorkEnv yst out left right)
      (pointAddDoubleInvCallState yst out left right)
      [pointAddDoubleInvStmt10, pointAddDoubleInvStmt11,
        pointAddDoubleInvStmt12, pointAddDoubleInvStmt13] =
    .ok (pointAddDoubleInvFinalWorkEnv yst out left right,
      pointAddDoubleInvFinalState yst out left right, .normal) := by
  rfl

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

theorem step_pointAddDoubleInvStmt (yst : EvmState) (out left right : U256)
    (hhi : (pointAddDoubleDenResult yst out left right).1.toNat < 2 ^ 128) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleInvInitialEnv yst out left right)
      (pointAddDoubleDenArgsState yst out left right)
      pointAddDoubleInvStmt (pointAddDoubleInvOutputEnv yst out left right)
      (pointAddDoubleInvFinalState yst out left right) .normal := by
  have hprefix := soundStmts (exec_pointAddDoubleInvPrefix yst out left right)
  have hcall := soundStmt (exec_pointAddDoubleInvCall yst out left right hhi)
  have houtput := soundStmts (exec_pointAddDoubleInvOutput yst out left right)
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddDoubleInvInitialEnv yst out left right)
      (pointAddDoubleDenArgsState yst out left right) pointAddDoubleInvBody
      (pointAddDoubleInvFinalWorkEnv yst out left right)
      (pointAddDoubleInvFinalState yst out left right) .normal := by
    rw [pointAddDoubleInvBody_eq]
    exact appendNormal hprefix (Step.seqCons hcall houtput)
  rw [pointAddDoubleInvStmt_eq]
  have hseq' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect pointAddDoubleInvBody ::
        pointAddBodyFuns)
      (pointAddDoubleInvInitialEnv yst out left right)
      (pointAddDoubleDenArgsState yst out left right) pointAddDoubleInvBody
      (pointAddDoubleInvFinalWorkEnv yst out left right)
      (pointAddDoubleInvFinalState yst out left right) .normal := by
    rw [hoist_pointAddDoubleInvBody]
    exact hseq
  have hblock := Step.block
    (D := Challenge.EvmProof.modexpExec.toDialect)
    (body := pointAddDoubleInvBody) hseq'
  simpa [pointAddDoubleInvOutputEnv, pointAddDoubleInvFinalWorkEnv,
    pointAddDoubleInvWorkEnv, pointAddDoubleInvInitialEnv, restore,
    bindZeros, VEnv.setMany, VEnv.set, VEnv.get] using hblock

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
