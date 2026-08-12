import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddPost

set_option warningAsError true

/-! Complete normal finite paths of G2MSM `pointAdd`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleAfterSkip (yst : EvmState) : EvmState :=
  pointAddEqFinalState (pointAddDoubleFinalState yst)

def pointAddFiniteDoubleFinal (yst : EvmState) : EvmState :=
  pointAddPostFinalState (pointAddDoubleAfterSkip yst)

theorem step_pointAddFiniteDouble (yst : EvmState) (out left right : U256)
    (heq : pointAddEqValue yst ≠ 0)
    (hy : pointAddDoubleYZero (pointAddDoubleState1 yst) = 0)
    (hhi : (fp2InvNorm (pointAddDoubleState6 yst) 2432).1.toNat <
      2 ^ 128)
    (heq2 : pointAddEqValue (pointAddDoubleFinalState yst) ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst
      ([pointAddStmt5, pointAddStmt6] ++ pointAddPostBody)
      (pointAddInitialEnv out left right)
      (pointAddFiniteDoubleFinal yst) .normal := by
  exact Step.seqCons (step_pointAddEqualRun yst out left right heq hy hhi)
    (Step.seqCons
      (step_pointAddUnequalSkip (pointAddDoubleFinalState yst)
        out left right heq2)
      (step_pointAddPost (pointAddDoubleAfterSkip yst) out left right))

def pointAddUnequalAfterEqualSkip (yst : EvmState) : EvmState :=
  pointAddEqFinalState yst

def pointAddUnequalAfterRun (yst : EvmState) : EvmState :=
  pointAddUnequalFinalState (pointAddUnequalAfterEqualSkip yst)

def pointAddFiniteUnequalFinal (yst : EvmState) : EvmState :=
  pointAddPostFinalState (pointAddUnequalAfterRun yst)

private theorem step_pointAddEqualSkip (yst : EvmState)
    (out left right : U256) (heq : pointAddEqValue yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddStmt5
      (pointAddInitialEnv out left right)
      (pointAddUnequalAfterEqualSkip yst) .normal := by
  rw [pointAddStmt5_eq]
  exact Step.ifFalse (step_pointAddEqualCondition yst out left right) heq

theorem step_pointAddFiniteUnequal (yst : EvmState)
    (out left right : U256) (heq1 : pointAddEqValue yst = 0)
    (heq2 : pointAddEqValue (pointAddUnequalAfterEqualSkip yst) = 0)
    (hhi : (fp2InvNorm
      (pointAddUnequalState2 (pointAddUnequalAfterEqualSkip yst))
      2432).1.toNat < 2 ^ 128) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst
      ([pointAddStmt5, pointAddStmt6] ++ pointAddPostBody)
      (pointAddInitialEnv out left right)
      (pointAddFiniteUnequalFinal yst) .normal := by
  exact Step.seqCons (step_pointAddEqualSkip yst out left right heq1)
    (Step.seqCons
      (step_pointAddUnequalRun (pointAddUnequalAfterEqualSkip yst)
        out left right heq2 hhi)
      (step_pointAddPost (pointAddUnequalAfterRun yst) out left right))

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
