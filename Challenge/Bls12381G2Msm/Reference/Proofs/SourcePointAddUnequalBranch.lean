import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddUnequalArithmetic

set_option warningAsError true

/-! Composition and skip cases of the finite unequal branch. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalState0 (yst : EvmState) : EvmState :=
  pointAddEqFinalState yst

def pointAddUnequalState1 (yst : EvmState) : EvmState :=
  pointAddUnequalYState (pointAddUnequalState0 yst)

def pointAddUnequalState2 (yst : EvmState) : EvmState :=
  pointAddUnequalXState (pointAddUnequalState1 yst)

def pointAddUnequalState3 (yst : EvmState) : EvmState :=
  pointAddUnequalInvState (pointAddUnequalState2 yst)

def pointAddUnequalFinalState (yst : EvmState) : EvmState :=
  pointAddUnequalSlopeState (pointAddUnequalState3 yst)

private theorem step_pointAddUnequalBody (yst : EvmState)
    (out left right : U256)
    (hhi : (fp2InvNorm (pointAddUnequalState2 yst) 2432).1.toNat <
      2 ^ 128) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) (pointAddUnequalState0 yst)
      (.block pointAddUnequalBody) (pointAddInitialEnv out left right)
      (pointAddUnequalFinalState yst) .normal := by
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddUnequalState0 yst) pointAddUnequalBody
      (pointAddInitialEnv out left right)
      (pointAddUnequalFinalState yst) .normal := by
    rw [pointAddUnequalBody_eq]
    exact Step.seqCons
      (step_pointAddUnequalYDiff (pointAddUnequalState0 yst) out left right)
      (Step.seqCons
        (step_pointAddUnequalXDiff (pointAddUnequalState1 yst) out left right)
        (Step.seqCons
          (step_pointAddUnequalInverse (pointAddUnequalState2 yst)
            out left right hhi)
          (Step.seqCons
            (step_pointAddUnequalSlope (pointAddUnequalState3 yst)
              out left right)
            Step.seqNil)))
  have hblock := Step.block (D := Challenge.EvmProof.modexpExec.toDialect)
    (body := pointAddUnequalBody) hseq
  simpa [restore, pointAddInitialEnv] using hblock

theorem step_pointAddUnequalRun (yst : EvmState) (out left right : U256)
    (heq : pointAddEqValue yst = 0)
    (hhi : (fp2InvNorm (pointAddUnequalState2 yst) 2432).1.toNat <
      2 ^ 128) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddStmt6
      (pointAddInitialEnv out left right)
      (pointAddUnequalFinalState yst) .normal := by
  rw [pointAddStmt6_eq]
  have hnonzero : b2w (pointAddEqValue yst = 0) ≠ (0 : U256) := by
    simp [heq, b2w]
  exact Step.ifTrue (step_pointAddUnequalCondition yst out left right)
    hnonzero (step_pointAddUnequalBody yst out left right hhi)

theorem step_pointAddUnequalSkip (yst : EvmState) (out left right : U256)
    (heq : pointAddEqValue yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddStmt6
      (pointAddInitialEnv out left right) (pointAddEqFinalState yst)
      .normal := by
  rw [pointAddStmt6_eq]
  have hzero : b2w (pointAddEqValue yst = 0) = (0 : U256) := by
    simp only [b2w]
    rw [if_neg (by simpa using heq)]
  exact Step.ifFalse (step_pointAddUnequalCondition yst out left right) hzero

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
