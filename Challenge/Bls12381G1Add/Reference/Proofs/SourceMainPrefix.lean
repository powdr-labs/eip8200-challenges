import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainCurveLawful

set_option warningAsError true

/-! # Frozen G1ADD canonical point-validation prefix -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

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

private theorem step_append_normal {funs V st pre Vmid stmid suffix Vend stend outcome}
    (hprefix : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      pre Vmid stmid .normal)
    (hsuffix : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs Vmid stmid
      suffix Vend stend outcome) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      (pre ++ suffix) Vend stend outcome := by
  induction pre generalizing V st Vmid stmid with
  | nil =>
    cases hprefix
    simpa using hsuffix
  | cons head rest ih =>
    cases hprefix with
    | seqCons hhead htail =>
      simpa using Step.seqCons hhead (ih htail hsuffix)
    | seqStop _ hnot => exact (hnot rfl).elim

/-- The length check, eight calldata stores, padding check, and four canonical
field checks reach the point scope with the exact decoded memory state. -/
theorem step_mainDecodePrefix_success (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainDecodePrefix [] (mainAfterCanonicalReads yst) .normal := by
  have hlength := sound_execStmt (exec_mainLength_success yst hsize)
  have hstores := sound_execStmts (exec_mainStores yst)
  have hpadding' := sound_execStmt (exec_mainPadding_success yst hpadding)
  have hcanonical' := sound_execStmt
    (exec_mainCanonical_success yst hcanonical)
  have htail := Step.seqCons hpadding'
    (Step.seqCons hcanonical' Step.seqNil)
  have hstoresTail := step_append_normal hstores htail
  simpa [mainDecodePrefix] using Step.seqCons hlength hstoresTail

theorem step_mainDecodePrefix_padding_reject (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainDecodePrefix [] (mainInvalidState (mainAfterPaddingReads yst))
      .halt := by
  have hlength := sound_execStmt (exec_mainLength_success yst hsize)
  have hstores := sound_execStmts (exec_mainStores yst)
  have hpadding' := sound_execStmt (exec_mainPadding_reject yst hpadding)
  have htail : ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainDecodedState yst) [mainPaddingStmt, mainCanonicalStmt]
      [] (mainInvalidState (mainAfterPaddingReads yst)) .halt :=
    Step.seqStop hpadding' (by decide)
  have hstoresTail := step_append_normal hstores htail
  simpa [mainDecodePrefix] using Step.seqCons hlength hstoresTail

theorem step_mainDecodePrefix_canonical_reject (yst : EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainDecodePrefix [] (mainInvalidState (mainAfterCanonicalReads yst))
      .halt := by
  have hlength := sound_execStmt (exec_mainLength_success yst hsize)
  have hstores := sound_execStmts (exec_mainStores yst)
  have hpadding' := sound_execStmt (exec_mainPadding_success yst hpadding)
  have hcanonical' := sound_execStmt
    (exec_mainCanonical_reject yst hcanonical)
  have htail : ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainDecodedState yst) [mainPaddingStmt, mainCanonicalStmt]
      [] (mainInvalidState (mainAfterCanonicalReads yst)) .halt :=
    Step.seqCons hpadding' (Step.seqStop hcanonical' (by decide))
  have hstoresTail := step_append_normal hstores htail
  simpa [mainDecodePrefix] using Step.seqCons hlength hstoresTail

/-- The two infinity predicates and both eager `onCurve` calls reach the exact
validated-pair state. The next source statement is the both-infinity return. -/
theorem step_mainPointValidation_success (yst : EvmState)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainAfterCanonicalReads yst) mainPointValidationPrefix
      (mainPointEnv yst) (mainValidatedState yst) .normal := by
  have hinf1 := sound_execStmt (exec_mainInf1 yst)
  have hinf2 := sound_execStmt (exec_mainInf2 yst)
  exact Step.seqCons hinf1 (Step.seqCons hinf2
    (Step.seqCons (step_mainCurve1_success yst hcurve1)
      (Step.seqCons (step_mainCurve2_success yst hcurve2) Step.seqNil)))

theorem step_mainPointValidation_curve1_reject (yst : EvmState)
    (hcurve1 : mainCurve1ConditionValue yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainAfterCanonicalReads yst) mainPointValidationPrefix
      (mainPointEnv yst) (mainInvalidState (mainAfterCurve1 yst)) .halt := by
  have hinf1 := sound_execStmt (exec_mainInf1 yst)
  have hinf2 := sound_execStmt (exec_mainInf2 yst)
  exact Step.seqCons hinf1 (Step.seqCons hinf2
    (Step.seqStop (step_mainCurve1_reject yst hcurve1) (by decide)))

theorem step_mainPointValidation_curve2_reject (yst : EvmState)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainAfterCanonicalReads yst) mainPointValidationPrefix
      (mainPointEnv yst) (mainInvalidState (mainValidatedState yst)) .halt := by
  have hinf1 := sound_execStmt (exec_mainInf1 yst)
  have hinf2 := sound_execStmt (exec_mainInf2 yst)
  exact Step.seqCons hinf1 (Step.seqCons hinf2
    (Step.seqCons (step_mainCurve1_success yst hcurve1)
      (Step.seqStop (step_mainCurve2_reject yst hcurve2) (by decide))))

theorem mainPointValidation_success_iff (yst : EvmState)
    (hcanonical : mainCanonicalValue yst ≠ 0) :
    mainCurve1ConditionValue yst = 0 ∧
        mainCurve2ConditionValue yst = 0 ↔
      (mainInf1 yst ≠ 0#256 ∨
        Challenge.Bls12381.ProofSupport.G1Affine.OnCurve (mainAffine1 yst)) ∧
      (mainInf2 yst ≠ 0#256 ∨
        Challenge.Bls12381.ProofSupport.G1Affine.OnCurve (mainAffine2 yst)) := by
  rcases (mainCanonicalValue_ne_zero_iff yst).mp hcanonical with
    ⟨hx1, hy1, hx2, hy2⟩
  rw [mainCurve1ConditionValue_eq_zero_iff yst hx1 hy1,
    mainCurve2ConditionValue_eq_zero_iff yst hx2 hy2]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
