import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFullMulFinal

set_option warningAsError true

/-! Relational composition of the staged G1MSM `fullMul` body. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

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

theorem fullMulBody_eq_stages :
    fullMulBody = fullMulP00Block ++ (fullMulP10Block ++
      (fullMulP01Block ++ (fullMulMiddleBlock ++ fullMulFinalBlock))) := by
  rfl

theorem step_fullMulBodyStmts (ahi alo bhi blo : U256) (yst : EvmState) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect fullMulBodyFuns
      (fullMulInitialEnv ahi alo bhi blo) yst fullMulBody
      (fullMulFinalEnv ahi alo bhi blo) yst .normal := by
  have hp00 := sound_execStmts (exec_fullMulP00 ahi alo bhi blo yst)
  have hp10 := sound_execStmts (exec_fullMulP10 ahi alo bhi blo yst)
  have hp01 := sound_execStmts (exec_fullMulP01 ahi alo bhi blo yst)
  have hmiddle := sound_execStmts (exec_fullMulMiddle ahi alo bhi blo yst)
  have hfinal := sound_execStmts (exec_fullMulFinal ahi alo bhi blo yst)
  rw [fullMulBody_eq_stages]
  exact step_append_normal hp00 (step_append_normal hp10
    (step_append_normal hp01 (step_append_normal hmiddle hfinal)))

def fullMulBodyResultEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (fullMulInitialEnv ahi alo bhi blo)
    (fullMulFinalEnv ahi alo bhi blo)

theorem step_fullMulBody (ahi alo bhi blo : U256) (yst : EvmState) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect sourceFuns
      (fullMulInitialEnv ahi alo bhi blo) yst (.block fullMulBody)
      (fullMulBodyResultEnv ahi alo bhi blo) yst .normal := by
  unfold fullMulBodyResultEnv
  apply Step.block
  rw [hoist_fullMulBody]
  exact step_fullMulBodyStmts ahi alo bhi blo yst

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
