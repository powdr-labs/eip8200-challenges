import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2InvImag
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Big-step composition of frozen G2MSM `fp2Inv`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem soundStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt Challenge.EvmProof.modexpExec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect funs V st stmt V' st' outcome :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.1
    _ _ _ _ _ _ _ h

private theorem soundStmts {n funs V st stmts V' st' outcome}
    (h : Interp.execStmts Challenge.EvmProof.modexpExec n funs V st stmts =
      .ok (V', st', outcome)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st stmts V' st' outcome :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.2.1
    _ _ _ _ _ _ _ h

private theorem appendNormal {funs V st pre Vmid stmid suffix Vend stend outcome}
    (hp : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st pre
      Vmid stmid .normal)
    (hs : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs Vmid stmid suffix
      Vend stend outcome) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st (pre ++ suffix)
      Vend stend outcome := by
  induction pre generalizing V st Vmid stmid with
  | nil => cases hp; simpa using hs
  | cons head rest ih =>
    cases hp with
    | seqCons hh ht => simpa using Step.seqCons hh (ih ht hs)
    | seqStop _ hn => exact (hn rfl).elim

def fp2InvBodyResultEnv (yst : EvmState) (out a : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (fp2InvInitialEnv out a) (fp2InvImagEnv yst out a)

theorem step_fp2InvBodyStmts (yst : EvmState) (out a : U256)
    (hhi : (fp2InvNorm yst a).1.toNat < 2 ^ 128) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect fp2InvBodyFuns
      (fp2InvInitialEnv out a) yst fp2InvBody
      (fp2InvImagEnv yst out a) (fp2InvFinalState yst out a) .normal := by
  have p0 := Step.seqCons (soundStmt (exec_fp2InvStmt0 yst out a))
    (soundStmts (exec_fp2InvSquare0Stores yst out a))
  have p1 := Step.seqCons (soundStmt (exec_fp2InvStmt3 yst out a))
    (soundStmts (exec_fp2InvSquare1Stores yst out a))
  have pn := Step.seqCons (soundStmt (exec_fp2InvStmt6 yst out a))
    (Step.seqNil (V := fp2InvNormEnv yst out a)
      (st := fp2InvAfterNormReads yst a))
  have pi := Step.seqCons (soundStmt (exec_fp2InvStmt7 yst out a hhi))
    (soundStmts (exec_fp2InvScalarStores yst out a))
  have pr := Step.seqCons (soundStmt (exec_fp2InvStmt10 yst out a))
    (soundStmts (exec_fp2InvRealStores yst out a))
  have pg := Step.seqCons (soundStmt (exec_fp2InvStmt13 yst out a))
    (Step.seqNil (V := fp2InvNegEnv yst out a)
      (st := fp2InvAfterNegReads yst out a))
  have pm := Step.seqCons (soundStmt (exec_fp2InvStmt14 yst out a))
    (soundStmts (exec_fp2InvImagStores yst out a))
  rw [fp2InvBody_eq]
  exact appendNormal p0 (appendNormal p1 (appendNormal pn
    (appendNormal pi (appendNormal pr (appendNormal pg pm)))))

theorem step_fp2InvBody (yst : EvmState) (out a : U256)
    (hhi : (fp2InvNorm yst a).1.toNat < 2 ^ 128) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect fp2InvFuns
      (fp2InvInitialEnv out a) yst (.block fp2InvBody)
      (fp2InvBodyResultEnv yst out a) (fp2InvFinalState yst out a)
      .normal := by
  rw [fp2InvBodyResultEnv]
  apply Step.block
  rw [fp2InvBodyFuns_eq]
  exact step_fp2InvBodyStmts yst out a hhi

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
