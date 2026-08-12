import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainPointDispatcher
import YulEvmCompiler.Optimizer.Implementation.StackLayoutSound

set_option warningAsError true

/-! # Complete frozen G2ADD point scope -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem step_append_normal
    {funs V st pre Vmid stmid suffix Vend stend outcome}
    (hprefix : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      pre Vmid stmid .normal)
    (hsuffix : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs Vmid stmid
      suffix Vend stend outcome) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      (pre ++ suffix) Vend stend outcome := by
  induction pre generalizing V st Vmid stmid with
  | nil => cases hprefix; simpa using hsuffix
  | cons head rest ih =>
    cases hprefix with
    | seqCons hhead htail => simpa using Step.seqCons hhead (ih htail hsuffix)
    | seqStop _ hnot => exact (hnot rfl).elim

private theorem step_append_halt
    {funs V st pre Vend stend suffix}
    (hprefix : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      pre Vend stend .halt) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      (pre ++ suffix) Vend stend .halt := by
  induction pre generalizing V st Vend stend with
  | nil => cases hprefix
  | cons head rest ih =>
    cases hprefix with
    | seqCons hhead htail => simpa using Step.seqCons hhead (ih htail)
    | seqStop hhead hnot => exact Step.seqStop hhead hnot

private theorem mainPointScopeBody_decompose : mainPointScopeBody =
    mainPointValidationPrefix ++ mainPointDispatcherBody := by rfl

theorem step_mainPointScope_finite (yst : EvmState)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainAfterValidationReads yst) mainPointScope
      [] (mainValidatedState yst) .normal := by
  have hvalidation : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) [] (mainAfterValidationReads yst)
      mainPointValidationPrefix (mainPointEnv yst)
      (mainValidatedState yst) .normal :=
    YulEvmCompiler.Optimizer.Step.emptyScope_congr
      (step_mainPointValidation_success yst hcurve1 hcurve2)
      (YulEvmCompiler.Optimizer.EmptyScopeRel.add mainFuns)
  have hdispatcher : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainValidatedState yst)
      mainPointDispatcherBody (mainPointEnv yst)
      (mainValidatedState yst) .normal :=
    YulEvmCompiler.Optimizer.Step.emptyScope_congr
      (step_mainPointDispatcher_finite yst hfirst hsecond)
      (YulEvmCompiler.Optimizer.EmptyScopeRel.add mainFuns)
  have hcombined : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) [] (mainAfterValidationReads yst)
      mainPointScopeBody (mainPointEnv yst)
      (mainValidatedState yst) .normal := by
    rw [mainPointScopeBody_decompose]
    exact step_append_normal hvalidation hdispatcher
  have hbody : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect mainPointScopeBody ::
        mainFuns) [] (mainAfterValidationReads yst) mainPointScopeBody
      (mainPointEnv yst) (mainValidatedState yst) .normal := by
    have hhoist : hoist Challenge.EvmProof.modexpExec.toDialect
        mainPointScopeBody = [] := by rfl
    rw [hhoist]
    exact hcombined
  have hblock := Step.block
    (D := Challenge.EvmProof.modexpExec.toDialect) hbody
  have hscope : mainPointScope = .block mainPointScopeBody := by rfl
  rw [hscope]
  simpa [restore] using hblock

private theorem step_mainPointScope_of_dispatcher (yst stend : EvmState)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hdispatch : ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst)
      mainPointDispatcherBody (mainPointEnv yst) stend .halt) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainAfterValidationReads yst) mainPointScope [] stend .halt := by
  have hvalidation : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) [] (mainAfterValidationReads yst)
      mainPointValidationPrefix (mainPointEnv yst)
      (mainValidatedState yst) .normal :=
    YulEvmCompiler.Optimizer.Step.emptyScope_congr
      (step_mainPointValidation_success yst hcurve1 hcurve2)
      (YulEvmCompiler.Optimizer.EmptyScopeRel.add mainFuns)
  have hdispatcher : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainValidatedState yst)
      mainPointDispatcherBody (mainPointEnv yst) stend .halt :=
    YulEvmCompiler.Optimizer.Step.emptyScope_congr hdispatch
      (YulEvmCompiler.Optimizer.EmptyScopeRel.add mainFuns)
  have hcombined : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) [] (mainAfterValidationReads yst)
      mainPointScopeBody (mainPointEnv yst) stend .halt := by
    rw [mainPointScopeBody_decompose]
    exact step_append_normal hvalidation hdispatcher
  have hbody : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect mainPointScopeBody ::
        mainFuns) [] (mainAfterValidationReads yst) mainPointScopeBody
      (mainPointEnv yst) stend .halt := by
    have hhoist : hoist Challenge.EvmProof.modexpExec.toDialect
        mainPointScopeBody = [] := by rfl
    rw [hhoist]
    exact hcombined
  have hblock := Step.block
    (D := Challenge.EvmProof.modexpExec.toDialect) hbody
  have hscope : mainPointScope = .block mainPointScopeBody := by rfl
  rw [hscope]
  simpa [restore] using hblock

theorem step_mainPointScope_bothInfinity (yst : EvmState)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hboth : mainBothInfinityValue yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainAfterValidationReads yst) mainPointScope []
      (mainBothInfinityReturnState yst) .halt :=
  step_mainPointScope_of_dispatcher yst _ hcurve1 hcurve2
    (step_mainPointDispatcher_bothInfinity yst hboth)

theorem step_mainPointScope_firstInfinity (yst : EvmState)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst ≠ 0) (hsecond : mainInf2 yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainAfterValidationReads yst) mainPointScope []
      (mainFirstInfinityReturnState yst) .halt :=
  step_mainPointScope_of_dispatcher yst _ hcurve1 hcurve2
    (step_mainPointDispatcher_firstInfinity yst hfirst hsecond)

theorem step_mainPointScope_secondInfinity (yst : EvmState)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainAfterValidationReads yst) mainPointScope []
      (mainSecondInfinityReturnState yst) .halt :=
  step_mainPointScope_of_dispatcher yst _ hcurve1 hcurve2
    (step_mainPointDispatcher_secondInfinity yst hfirst hsecond)

private theorem step_mainPointScope_of_validationHalt (yst stend : EvmState)
    (hvalidation : ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainAfterValidationReads yst) mainPointValidationPrefix
      (mainPointEnv yst) stend .halt) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainAfterValidationReads yst) mainPointScope [] stend .halt := by
  have hvalidation' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) [] (mainAfterValidationReads yst)
      mainPointValidationPrefix (mainPointEnv yst) stend .halt :=
    YulEvmCompiler.Optimizer.Step.emptyScope_congr hvalidation
      (YulEvmCompiler.Optimizer.EmptyScopeRel.add mainFuns)
  have hbody : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect mainPointScopeBody ::
        mainFuns) [] (mainAfterValidationReads yst) mainPointScopeBody
      (mainPointEnv yst) stend .halt := by
    have hhoist : hoist Challenge.EvmProof.modexpExec.toDialect
        mainPointScopeBody = [] := by rfl
    rw [hhoist, mainPointScopeBody_decompose]
    exact step_append_halt hvalidation'
  have hblock := Step.block
    (D := Challenge.EvmProof.modexpExec.toDialect) hbody
  have hscope : mainPointScope = .block mainPointScopeBody := by rfl
  rw [hscope]
  simpa [restore] using hblock

theorem step_mainPointScope_curve1_reject (yst : EvmState)
    (hcurve1 : mainCurve1ConditionValue yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainAfterValidationReads yst) mainPointScope []
      (mainInvalidState (mainAfterCurve1 yst)) .halt :=
  step_mainPointScope_of_validationHalt yst _
    (step_mainPointValidation_curve1_reject yst hcurve1)

theorem step_mainPointScope_curve2_reject (yst : EvmState)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainAfterValidationReads yst) mainPointScope []
      (mainInvalidState (mainValidatedState yst)) .halt :=
  step_mainPointScope_of_validationHalt yst _
    (step_mainPointValidation_curve2_reject yst hcurve1 hcurve2)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
