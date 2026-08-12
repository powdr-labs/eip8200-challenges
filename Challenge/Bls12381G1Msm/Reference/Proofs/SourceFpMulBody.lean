import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulOutput

set_option warningAsError true

/-! Relational composition of the staged G1MSM `fpMul` body. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem sound_execStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt Challenge.EvmProof.modexpExec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect funs V st stmt
      V' st' outcome :=
  (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hbuiltin =>
      Challenge.EvmProof.modexpBuiltinFn_sound hbuiltin) n).2.2.1
    _ _ _ _ _ _ _ h

private theorem sound_execStmts {n funs V st stmts V' st' outcome}
    (h : Interp.execStmts Challenge.EvmProof.modexpExec n funs V st stmts =
      .ok (V', st', outcome)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st stmts
      V' st' outcome :=
  (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hbuiltin =>
      Challenge.EvmProof.modexpBuiltinFn_sound hbuiltin) n).2.2.2.1
    _ _ _ _ _ _ _ h

private theorem step_append_normal
    {funs V st pre Vmid stmid suffix Vend stend outcome}
    (hpre : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      pre Vmid stmid .normal)
    (hsuffix : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs Vmid stmid
      suffix Vend stend outcome) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      (pre ++ suffix) Vend stend outcome := by
  induction pre generalizing V st Vmid stmid with
  | nil =>
    cases hpre
    simpa using hsuffix
  | cons head rest ih =>
    cases hpre with
    | seqCons hhead htail =>
      simpa using Step.seqCons hhead (ih htail hsuffix)
    | seqStop _ hnot => exact (hnot rfl).elim

theorem fpMulBody_eq_stages : fpMulBody =
    [fpMulStmt0] ++ (fpMulInputStores ++
      ([fpMulStmt6] ++ fpMulOutputBlock)) := by
  rfl

theorem step_fpMulBodyStmts (ahi alo bhi blo : U256) (yst : EvmState) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect fpMulBodyFuns
      (fpMulInitialEnv ahi alo bhi blo) yst fpMulBody
      (fpMulReturnEnv yst ahi alo bhi blo)
      (fpMulFinalState yst ahi alo bhi blo) .normal := by
  have hproduct := step_fpMulProduct ahi alo bhi blo yst
  have hstores := sound_execStmts
    (exec_fpMulInputStores ahi alo bhi blo yst)
  have hcall := sound_execStmt (exec_fpMulCall ahi alo bhi blo yst)
  have houtput := sound_execStmts (exec_fpMulOutput ahi alo bhi blo yst)
  have hcallOutput : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      fpMulBodyFuns (fpMulInitialEnv ahi alo bhi blo)
      (fpMulInputState yst ahi alo bhi blo)
      ([fpMulStmt6] ++ fpMulOutputBlock)
      (fpMulReturnEnv yst ahi alo bhi blo)
      (fpMulFinalState yst ahi alo bhi blo) .normal :=
    Step.seqCons hcall houtput
  have hstoresTail : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      fpMulBodyFuns (fpMulInitialEnv ahi alo bhi blo)
      (fpMulProductState yst ahi alo bhi blo)
      (fpMulInputStores ++ ([fpMulStmt6] ++ fpMulOutputBlock))
      (fpMulReturnEnv yst ahi alo bhi blo)
      (fpMulFinalState yst ahi alo bhi blo) .normal :=
    step_append_normal hstores hcallOutput
  rw [fpMulBody_eq_stages]
  exact Step.seqCons hproduct hstoresTail

def fpMulBodyResultEnv (yst : EvmState) (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (fpMulInitialEnv ahi alo bhi blo)
    (fpMulReturnEnv yst ahi alo bhi blo)

theorem fpMulBodyResultEnv_hi (yst : EvmState) (ahi alo bhi blo : U256) :
    (VEnv.get (fpMulBodyResultEnv yst ahi alo bhi blo) "\x0077").getD 0 =
      (fpMulResult yst ahi alo bhi blo).1 := by
  rfl

theorem fpMulBodyResultEnv_lo (yst : EvmState) (ahi alo bhi blo : U256) :
    (VEnv.get (fpMulBodyResultEnv yst ahi alo bhi blo) "\x0078").getD 0 =
      (fpMulResult yst ahi alo bhi blo).2 := by
  rfl

theorem step_fpMulBody (ahi alo bhi blo : U256) (yst : EvmState) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect sourceFuns
      (fpMulInitialEnv ahi alo bhi blo) yst (.block fpMulBody)
      (fpMulBodyResultEnv yst ahi alo bhi blo)
      (fpMulFinalState yst ahi alo bhi blo) .normal := by
  unfold fpMulBodyResultEnv
  apply Step.block
  rw [hoist_fpMulBody]
  exact step_fpMulBodyStmts ahi alo bhi blo yst

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
