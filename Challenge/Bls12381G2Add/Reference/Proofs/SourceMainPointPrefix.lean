import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainSecondInfinity

set_option warningAsError true

/-! # Frozen G2ADD point-scope validation prefix -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainPointValidationPrefix : Block Op := mainPointScopeBody.take 4

theorem mainPointValidationPrefix_eq : mainPointValidationPrefix =
    [mainPointStmt0, mainPointStmt1, mainPointStmt2, mainPointStmt3] := by rfl

private theorem sound_execStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt Challenge.EvmProof.modexpExec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect funs V st stmt
      V' st' outcome :=
  (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.1
    _ _ _ _ _ _ _ h

theorem step_mainPointValidation_success (yst : EvmState)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainAfterValidationReads yst) mainPointValidationPrefix
      (mainPointEnv yst) (mainValidatedState yst) .normal := by
  rw [mainPointValidationPrefix_eq]
  exact Step.seqCons (sound_execStmt (exec_mainInf1 yst))
    (Step.seqCons (sound_execStmt (exec_mainInf2 yst))
      (Step.seqCons (step_mainCurve1_success yst hcurve1)
        (Step.seqCons (step_mainCurve2_success yst hcurve2) Step.seqNil)))

theorem step_mainPointValidation_curve1_reject (yst : EvmState)
    (hcurve1 : mainCurve1ConditionValue yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainAfterValidationReads yst) mainPointValidationPrefix
      (mainPointEnv yst) (mainInvalidState (mainAfterCurve1 yst)) .halt := by
  rw [mainPointValidationPrefix_eq]
  exact Step.seqCons (sound_execStmt (exec_mainInf1 yst))
    (Step.seqCons (sound_execStmt (exec_mainInf2 yst))
      (Step.seqStop (step_mainCurve1_reject yst hcurve1) (by decide)))

theorem step_mainPointValidation_curve2_reject (yst : EvmState)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainAfterValidationReads yst) mainPointValidationPrefix
      (mainPointEnv yst) (mainInvalidState (mainValidatedState yst)) .halt := by
  rw [mainPointValidationPrefix_eq]
  exact Step.seqCons (sound_execStmt (exec_mainInf1 yst))
    (Step.seqCons (sound_execStmt (exec_mainInf2 yst))
      (Step.seqCons (step_mainCurve1_success yst hcurve1)
        (Step.seqStop (step_mainCurve2_reject yst hcurve2) (by decide))))

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
