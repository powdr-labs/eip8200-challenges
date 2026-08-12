import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteUnequalBranch

set_option warningAsError true

/-! # Complete frozen G2ADD finite dispatcher execution -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem mainFiniteBody_decompose : mainFiniteBody =
    mainFiniteStmt0 :: mainFiniteStmt1 :: mainPostBody := by rfl

theorem step_mainFiniteDispatcher_double (yst : EvmState)
    (hxeq1 : mainFiniteXEq1 yst ≠ 0)
    (hyeq : mainDoubleYEq yst ≠ 0)
    (hyzero : mainDoubleYZero yst = 0)
    (hinv : (fp2InvNorm (mainDoubleState3 yst) 2432).1.toNat < 2 ^ 128)
    (hxeq2 : mainDoubleXEq2 yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainValidatedState yst) mainFiniteBody []
      (mainPostReturnState (mainAfterDoubleXEq2 yst)) .halt := by
  rw [mainFiniteBody_decompose]
  exact Step.seqCons
    (step_mainFiniteEqual_double yst hxeq1 hyeq hyzero hinv)
    (Step.seqCons (step_mainFiniteUnequal_skip_after_double yst hxeq2)
      (step_mainPostBody (mainAfterDoubleXEq2 yst)))

theorem step_mainFiniteDispatcher_unequal (yst : EvmState)
    (hxeq1 : mainFiniteXEq1 yst = 0)
    (hxeq2 : mainFiniteXEq2 yst = 0)
    (hinv : (fp2InvNorm (mainUnequalState1 yst) 2432).1.toNat < 2 ^ 128) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainValidatedState yst) mainFiniteBody []
      (mainPostReturnState (mainUnequalFinalState yst)) .halt := by
  rw [mainFiniteBody_decompose]
  exact Step.seqCons (step_mainFiniteEqual_skip yst hxeq1)
    (Step.seqCons (step_mainFiniteUnequal_run yst hxeq2 hinv)
      (step_mainPostBody (mainUnequalFinalState yst)))

theorem step_mainFiniteDispatcher_opposite (yst : EvmState)
    (hxeq : mainFiniteXEq1 yst ≠ 0)
    (hyeq : mainDoubleYEq yst = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainValidatedState yst) mainFiniteBody []
      (mainFiniteClearReturnState (mainAfterDoubleYEq yst)) .halt := by
  rw [mainFiniteBody_decompose]
  exact Step.seqStop (step_mainFiniteEqual_opposite yst hxeq hyeq) (by decide)

theorem step_mainFiniteDispatcher_zeroY (yst : EvmState)
    (hxeq : mainFiniteXEq1 yst ≠ 0)
    (hyeq : mainDoubleYEq yst ≠ 0)
    (hyzero : mainDoubleYZero yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainValidatedState yst) mainFiniteBody []
      (mainFiniteClearReturnState (mainAfterDoubleYZero yst)) .halt := by
  rw [mainFiniteBody_decompose]
  exact Step.seqStop (step_mainFiniteEqual_zeroY yst hxeq hyeq hyzero)
    (by decide)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
