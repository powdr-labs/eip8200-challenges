import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainPointPrefix

set_option warningAsError true

/-! # Frozen G2ADD point-scope infinity dispatcher -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainPointDispatcherBody : Block Op := mainPointScopeBody.drop 4

theorem mainPointDispatcherBody_eq : mainPointDispatcherBody =
    [mainPointStmt4, mainPointStmt5, mainPointStmt6] := by rfl

theorem step_mainPointDispatcher_finite (yst : EvmState)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) mainPointDispatcherBody
      (mainPointEnv yst) (mainValidatedState yst) .normal := by
  have hboth : mainBothInfinityValue yst = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp [mainBothInfinityValue, hfirst]
  rw [mainPointDispatcherBody_eq]
  exact Step.seqCons (step_mainBothInfinity_continue yst hboth)
    (Step.seqCons (step_mainFirstInfinity_continue yst hfirst)
      (Step.seqCons (step_mainSecondInfinity_continue yst hsecond) Step.seqNil))

theorem step_mainPointDispatcher_bothInfinity (yst : EvmState)
    (hboth : mainBothInfinityValue yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) mainPointDispatcherBody
      (mainPointEnv yst) (mainBothInfinityReturnState yst) .halt := by
  rw [mainPointDispatcherBody_eq]
  exact Step.seqStop (step_mainBothInfinity_return yst hboth) (by decide)

theorem step_mainPointDispatcher_firstInfinity (yst : EvmState)
    (hfirst : mainInf1 yst ≠ 0) (hsecond : mainInf2 yst = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) mainPointDispatcherBody
      (mainPointEnv yst) (mainFirstInfinityReturnState yst) .halt := by
  have hboth : mainBothInfinityValue yst = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp [mainBothInfinityValue, hsecond]
  rw [mainPointDispatcherBody_eq]
  exact Step.seqCons (step_mainBothInfinity_continue yst hboth)
    (Step.seqStop (step_mainFirstInfinity_return yst hfirst) (by decide))

theorem step_mainPointDispatcher_secondInfinity (yst : EvmState)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) mainPointDispatcherBody
      (mainPointEnv yst) (mainSecondInfinityReturnState yst) .halt := by
  have hboth : mainBothInfinityValue yst = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp [mainBothInfinityValue, hfirst]
  rw [mainPointDispatcherBody_eq]
  exact Step.seqCons (step_mainBothInfinity_continue yst hboth)
    (Step.seqCons (step_mainFirstInfinity_continue yst hfirst)
      (Step.seqStop (step_mainSecondInfinity_return yst hsecond) (by decide)))

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
