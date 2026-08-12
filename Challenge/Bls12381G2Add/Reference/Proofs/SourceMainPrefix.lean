import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteDispatcher

set_option warningAsError true

/-! # Frozen G2ADD decode and validity prefix composition -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainPrefixBody : Block Op := (Compilation.referenceCompiledBlock).drop 25 |>.take 18

theorem mainPrefixBody_eq : mainPrefixBody =
    mainLengthStmt :: mainStores ++ [mainValidationStmt] := by rfl

private theorem sound_execStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt Challenge.EvmProof.modexpExec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect funs V st stmt
      V' st' outcome :=
  (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.1
    _ _ _ _ _ _ _ h

private theorem sound_execStmts {n funs V st stmts V' st' outcome}
    (h : Interp.execStmts Challenge.EvmProof.modexpExec n funs V st stmts =
      .ok (V', st', outcome)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st stmts
      V' st' outcome :=
  (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.2.1
    _ _ _ _ _ _ _ h

private theorem step_append_normal
    {funs V st pre Vmid stmid suffix Vend stend outcome}
    (hp : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st pre
      Vmid stmid .normal)
    (hs : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs Vmid stmid
      suffix Vend stend outcome) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      (pre ++ suffix) Vend stend outcome := by
  induction pre generalizing V st Vmid stmid with
  | nil => cases hp; simpa using hs
  | cons head rest ih =>
    cases hp with
    | seqCons hh ht => simpa using Step.seqCons hh (ih ht hs)
    | seqStop _ hn => exact (hn rfl).elim

theorem step_mainStores (yst : EvmState) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainStores [] (mainDecodedState yst) .normal := by
  have h0 := sound_execStmts (exec_mainStores0 yst)
  have h1 := sound_execStmts (exec_mainStores1 yst)
  have h2 := sound_execStmts (exec_mainStores2 yst)
  have h3 := sound_execStmts (exec_mainStores3 yst)
  simpa [mainStores] using step_append_normal h0
    (step_append_normal h1 (step_append_normal h2 h3))

theorem step_mainPrefix_success (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainPrefixBody [] (mainAfterValidationReads yst) .normal := by
  rw [mainPrefixBody_eq]
  exact Step.seqCons (sound_execStmt (exec_mainLength_success yst hsize))
    (step_append_normal (step_mainStores yst)
      (Step.seqCons
        (sound_execStmt (exec_mainValidation_success yst hvalid)) Step.seqNil))

theorem step_mainPrefix_length_reject (yst : EvmState)
    (hfit : yst.env.calldata.length < 2 ^ 256)
    (hsize : yst.env.calldata.length ≠ 512) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainPrefixBody [] (mainInvalidState yst) .halt := by
  rw [mainPrefixBody_eq]
  exact Step.seqStop
    (sound_execStmt (exec_mainLength_reject yst hfit hsize)) (by decide)

theorem step_mainPrefix_validation_reject (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainPrefixBody []
      (mainInvalidState (mainAfterValidationReads yst)) .halt := by
  rw [mainPrefixBody_eq]
  exact Step.seqCons (sound_execStmt (exec_mainLength_success yst hsize))
    (step_append_normal (step_mainStores yst)
      (Step.seqStop
        (sound_execStmt (exec_mainValidation_reject yst hvalid)) (by decide)))

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
