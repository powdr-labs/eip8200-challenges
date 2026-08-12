import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainPrefix

set_option warningAsError true

/-! # Complete frozen G2ADD source runs -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainValidBody : Block Op := (Compilation.referenceCompiledBlock).drop 25

theorem mainValidBody_eq : mainValidBody =
    mainPrefixBody ++ mainPointScope :: mainFiniteBody := by rfl

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

private theorem step_append_halt
    {funs V st pre Vend stend suffix}
    (hp : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st pre
      Vend stend .halt) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      (pre ++ suffix) Vend stend .halt := by
  induction pre generalizing V st Vend stend with
  | nil => cases hp
  | cons head rest ih =>
    cases hp with
    | seqCons hh ht => simpa using Step.seqCons hh (ih ht)
    | seqStop hh hn => exact Step.seqStop hh hn

private theorem step_main_finite (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    {stend : EvmState}
    (htail : ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainValidatedState yst) mainFiniteBody [] stend .halt) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody [] stend .halt := by
  rw [mainValidBody_eq]
  exact step_append_normal (step_mainPrefix_success yst hsize hvalid)
    (Step.seqCons
      (step_mainPointScope_finite yst hcurve1 hcurve2 hfirst hsecond) htail)

theorem step_main_double (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq1 : mainFiniteXEq1 yst ≠ 0)
    (hyeq : mainDoubleYEq yst ≠ 0)
    (hyzero : mainDoubleYZero yst = 0)
    (hinv : (fp2InvNorm (mainDoubleState3 yst) 2432).1.toNat < 2 ^ 128)
    (hxeq2 : mainDoubleXEq2 yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody []
      (mainPostReturnState (mainAfterDoubleXEq2 yst)) .halt :=
  step_main_finite yst hsize hvalid hcurve1 hcurve2 hfirst hsecond
    (step_mainFiniteDispatcher_double yst hxeq1 hyeq hyzero hinv hxeq2)

theorem step_main_unequal (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq1 : mainFiniteXEq1 yst = 0)
    (hxeq2 : mainFiniteXEq2 yst = 0)
    (hinv : (fp2InvNorm (mainUnequalState1 yst) 2432).1.toNat < 2 ^ 128) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody [] (mainPostReturnState (mainUnequalFinalState yst)) .halt :=
  step_main_finite yst hsize hvalid hcurve1 hcurve2 hfirst hsecond
    (step_mainFiniteDispatcher_unequal yst hxeq1 hxeq2 hinv)

private theorem step_main_pointHalt (yst stend : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hpoint : ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterValidationReads yst) mainPointScope [] stend .halt) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody [] stend .halt := by
  rw [mainValidBody_eq]
  exact step_append_normal (step_mainPrefix_success yst hsize hvalid)
    (Step.seqStop hpoint (by decide))

theorem step_main_bothInfinity (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hboth : mainBothInfinityValue yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody [] (mainBothInfinityReturnState yst) .halt :=
  step_main_pointHalt yst _ hsize hvalid
    (step_mainPointScope_bothInfinity yst hcurve1 hcurve2 hboth)

theorem step_main_firstInfinity (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst ≠ 0) (hsecond : mainInf2 yst = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody [] (mainFirstInfinityReturnState yst) .halt :=
  step_main_pointHalt yst _ hsize hvalid
    (step_mainPointScope_firstInfinity yst hcurve1 hcurve2 hfirst hsecond)

theorem step_main_secondInfinity (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody [] (mainSecondInfinityReturnState yst) .halt :=
  step_main_pointHalt yst _ hsize hvalid
    (step_mainPointScope_secondInfinity yst hcurve1 hcurve2 hfirst hsecond)

theorem step_main_opposite (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq : mainFiniteXEq1 yst ≠ 0)
    (hyeq : mainDoubleYEq yst = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody []
      (mainFiniteClearReturnState (mainAfterDoubleYEq yst)) .halt :=
  step_main_finite yst hsize hvalid hcurve1 hcurve2 hfirst hsecond
    (step_mainFiniteDispatcher_opposite yst hxeq hyeq)

theorem step_main_zeroY (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq : mainFiniteXEq1 yst ≠ 0)
    (hyeq : mainDoubleYEq yst ≠ 0)
    (hyzero : mainDoubleYZero yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody []
      (mainFiniteClearReturnState (mainAfterDoubleYZero yst)) .halt :=
  step_main_finite yst hsize hvalid hcurve1 hcurve2 hfirst hsecond
    (step_mainFiniteDispatcher_zeroY yst hxeq hyeq hyzero)

theorem step_main_length_reject (yst : EvmState)
    (hfit : yst.env.calldata.length < 2 ^ 256)
    (hsize : yst.env.calldata.length ≠ 512) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody [] (mainInvalidState yst) .halt := by
  rw [mainValidBody_eq]
  exact step_append_halt (step_mainPrefix_length_reject yst hfit hsize)

theorem step_main_validation_reject (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody []
      (mainInvalidState (mainAfterValidationReads yst)) .halt := by
  rw [mainValidBody_eq]
  exact step_append_halt (step_mainPrefix_validation_reject yst hsize hvalid)

theorem step_main_curve1_reject (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody [] (mainInvalidState (mainAfterCurve1 yst)) .halt :=
  step_main_pointHalt yst _ hsize hvalid
    (step_mainPointScope_curve1_reject yst hcurve1)

theorem step_main_curve2_reject (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody [] (mainInvalidState (mainValidatedState yst)) .halt :=
  step_main_pointHalt yst _ hsize hvalid
    (step_mainPointScope_curve2_reject yst hcurve1 hcurve2)

private def isFunctionDefinition : Stmt Op → Bool
  | .funDef .. => true
  | _ => false

private theorem step_function_definitions
    (defs : Block Op) (hdefs : defs.all isFunctionDefinition = true)
    (funs : FunEnv Challenge.EvmProof.modexpExec.toDialect)
    (V : VEnv Challenge.EvmProof.modexpExec.toDialect) (yst : EvmState) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V yst defs
      V yst .normal := by
  induction defs with
  | nil => exact Step.seqNil
  | cons head tail ih =>
    have hp : isFunctionDefinition head = true ∧
        tail.all isFunctionDefinition = true := by simpa using hdefs
    cases head <;> simp only [isFunctionDefinition, Bool.false_eq_true] at hp
    all_goals try { exact False.elim hp.1 }
    case funDef => exact Step.seqCons Step.funDef (ih hp.2)

private theorem reference_function_prefix :
    ((Compilation.referenceCompiledBlock).take 25).all
      isFunctionDefinition = true := by rfl

private theorem reference_decompose : Compilation.referenceCompiledBlock =
    (Compilation.referenceCompiledBlock).take 25 ++ mainValidBody :=
  (List.take_append_drop 25 Compilation.referenceCompiledBlock).symm

theorem run_of_mainValid (yst stend : EvmState)
    (hmain : ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainValidBody [] stend .halt) :
    Run Challenge.Bls12381G2Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst [] stend .halt := by
  have hdefs := step_function_definitions
    ((Compilation.referenceCompiledBlock).take 25)
    reference_function_prefix mainFuns [] yst
  have hbody : ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      Compilation.referenceCompiledBlock [] stend .halt := by
    rw [reference_decompose]
    exact step_append_normal hdefs hmain
  have hblock := Step.block
    (D := Challenge.EvmProof.modexpExec.toDialect) hbody
  simpa [Run, mainFuns, restore] using hblock

theorem run_main_double (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq1 : mainFiniteXEq1 yst ≠ 0)
    (hyeq : mainDoubleYEq yst ≠ 0)
    (hyzero : mainDoubleYZero yst = 0)
    (hinv : (fp2InvNorm (mainDoubleState3 yst) 2432).1.toNat < 2 ^ 128)
    (hxeq2 : mainDoubleXEq2 yst ≠ 0) :
    Run Challenge.Bls12381G2Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainPostReturnState (mainAfterDoubleXEq2 yst)) .halt :=
  run_of_mainValid yst _ (step_main_double yst hsize hvalid hcurve1 hcurve2
    hfirst hsecond hxeq1 hyeq hyzero hinv hxeq2)

theorem run_main_unequal (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq1 : mainFiniteXEq1 yst = 0)
    (hxeq2 : mainFiniteXEq2 yst = 0)
    (hinv : (fp2InvNorm (mainUnequalState1 yst) 2432).1.toNat < 2 ^ 128) :
    Run Challenge.Bls12381G2Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainPostReturnState (mainUnequalFinalState yst)) .halt :=
  run_of_mainValid yst _ (step_main_unequal yst hsize hvalid hcurve1 hcurve2
    hfirst hsecond hxeq1 hxeq2 hinv)

theorem run_main_bothInfinity (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hboth : mainBothInfinityValue yst ≠ 0) :
    Run Challenge.Bls12381G2Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainBothInfinityReturnState yst) .halt :=
  run_of_mainValid yst _
    (step_main_bothInfinity yst hsize hvalid hcurve1 hcurve2 hboth)

theorem run_main_firstInfinity (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst ≠ 0) (hsecond : mainInf2 yst = 0) :
    Run Challenge.Bls12381G2Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainFirstInfinityReturnState yst) .halt :=
  run_of_mainValid yst _
    (step_main_firstInfinity yst hsize hvalid hcurve1 hcurve2 hfirst hsecond)

theorem run_main_secondInfinity (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst ≠ 0) :
    Run Challenge.Bls12381G2Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainSecondInfinityReturnState yst) .halt :=
  run_of_mainValid yst _
    (step_main_secondInfinity yst hsize hvalid hcurve1 hcurve2 hfirst hsecond)

theorem run_main_opposite (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq : mainFiniteXEq1 yst ≠ 0) (hyeq : mainDoubleYEq yst = 0) :
    Run Challenge.Bls12381G2Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainFiniteClearReturnState (mainAfterDoubleYEq yst)) .halt :=
  run_of_mainValid yst _ (step_main_opposite yst hsize hvalid hcurve1 hcurve2
    hfirst hsecond hxeq hyeq)

theorem run_main_zeroY (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq : mainFiniteXEq1 yst ≠ 0) (hyeq : mainDoubleYEq yst ≠ 0)
    (hyzero : mainDoubleYZero yst ≠ 0) :
    Run Challenge.Bls12381G2Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainFiniteClearReturnState (mainAfterDoubleYZero yst)) .halt :=
  run_of_mainValid yst _ (step_main_zeroY yst hsize hvalid hcurve1 hcurve2
    hfirst hsecond hxeq hyeq hyzero)

theorem run_main_length_reject (yst : EvmState)
    (hfit : yst.env.calldata.length < 2 ^ 256)
    (hsize : yst.env.calldata.length ≠ 512) :
    Run Challenge.Bls12381G2Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainInvalidState yst) .halt :=
  run_of_mainValid yst _ (step_main_length_reject yst hfit hsize)

theorem run_main_validation_reject (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst = 0) :
    Run Challenge.Bls12381G2Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainInvalidState (mainAfterValidationReads yst)) .halt :=
  run_of_mainValid yst _ (step_main_validation_reject yst hsize hvalid)

theorem run_main_curve1_reject (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst ≠ 0) :
    Run Challenge.Bls12381G2Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainInvalidState (mainAfterCurve1 yst)) .halt :=
  run_of_mainValid yst _
    (step_main_curve1_reject yst hsize hvalid hcurve1)

theorem run_main_curve2_reject (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst ≠ 0) :
    Run Challenge.Bls12381G2Add.ProofSupport.Yul.localDialect
      Compilation.referenceCompiledBlock yst []
      (mainInvalidState (mainValidatedState yst)) .halt :=
  run_of_mainValid yst _
    (step_main_curve2_reject yst hsize hvalid hcurve1 hcurve2)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
