import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulImag
import Challenge.EvmProof.ExecSound

set_option warningAsError true
/-! # Big-step composition of frozen G2ADD `fp2Mul` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
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
    (hp : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st pre Vmid stmid .normal)
    (hs : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs Vmid stmid suffix Vend stend outcome) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st (pre ++ suffix) Vend stend outcome := by
  induction pre generalizing V st Vmid stmid with
  | nil => cases hp; simpa using hs
  | cons head rest ih =>
    cases hp with
    | seqCons hh ht => simpa using Step.seqCons hh (ih ht hs)
    | seqStop _ hn => exact (hn rfl).elim

def fp2MulBodyResultEnv (yst : EvmState) (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (fp2MulInitialEnv out a b) (fp2MulImagEnv yst out a b)

theorem step_fp2MulBodyStmts (yst : EvmState) (out a b : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect fp2MulBodyFuns
      (fp2MulInitialEnv out a b) yst fp2MulBody
      (fp2MulImagEnv yst out a b) (fp2MulFinalState yst out a b) .normal := by
  have p0 := Step.seqCons (soundStmt (exec_fp2MulStmt0 yst out a b))
    (soundStmts (exec_fp2MulV0Stores yst out a b))
  have p1 := Step.seqCons (soundStmt (exec_fp2MulStmt3 yst out a b))
    (soundStmts (exec_fp2MulV1Stores yst out a b))
  have pr := Step.seqCons (soundStmt (exec_fp2MulStmt6 yst out a b))
    (soundStmts (exec_fp2MulRealStores yst out a b))
  have pa := Step.seqCons (soundStmt (exec_fp2MulStmt9 yst out a b))
    (soundStmts (exec_fp2MulSumAStores yst out a b))
  have pb := Step.seqCons (soundStmt (exec_fp2MulStmt12 yst out a b))
    (soundStmts (exec_fp2MulSumBStores yst out a b))
  have pc := Step.seqCons (soundStmt (exec_fp2MulStmt15 yst out a b))
    (soundStmts (exec_fp2MulCrossStores yst out a b))
  have ps := Step.seqCons (soundStmt (exec_fp2MulStmt18 yst out a b))
    (soundStmts (exec_fp2MulVSumStores yst out a b))
  have pi := Step.seqCons (soundStmt (exec_fp2MulStmt21 yst out a b))
    (soundStmts (exec_fp2MulImagStores yst out a b))
  rw [fp2MulBody_eq]
  exact appendNormal p0 (appendNormal p1 (appendNormal pr (appendNormal pa
    (appendNormal pb (appendNormal pc (appendNormal ps pi))))))

theorem step_fp2MulBody (yst : EvmState) (out a b : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect fp2MulFuns
      (fp2MulInitialEnv out a b) yst (.block fp2MulBody)
      (fp2MulBodyResultEnv yst out a b) (fp2MulFinalState yst out a b) .normal := by
  rw [fp2MulBodyResultEnv]
  apply Step.block
  rw [fp2MulBodyFuns_eq]
  exact step_fp2MulBodyStmts yst out a b

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
