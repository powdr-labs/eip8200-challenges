import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddDoubleArithmetic

set_option warningAsError true

/-! Composition of the normal finite doubling branch of G2MSM `pointAdd`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleState0 (yst : EvmState) : EvmState :=
  pointAddEqFinalState yst

def pointAddDoubleState1 (yst : EvmState) : EvmState :=
  pointAddDoubleYSumState (pointAddDoubleState0 yst)

def pointAddDoubleState2 (yst : EvmState) : EvmState :=
  pointAddAfterDoubleYZero (pointAddDoubleState1 yst)

def pointAddDoubleState3 (yst : EvmState) : EvmState :=
  pointAddDoubleSquareState (pointAddDoubleState2 yst)

def pointAddDoubleState4 (yst : EvmState) : EvmState :=
  pointAddDoubleNum2State (pointAddDoubleState3 yst)

def pointAddDoubleState5 (yst : EvmState) : EvmState :=
  pointAddDoubleNum3State (pointAddDoubleState4 yst)

def pointAddDoubleState6 (yst : EvmState) : EvmState :=
  pointAddDoubleDenState (pointAddDoubleState5 yst)

def pointAddDoubleState7 (yst : EvmState) : EvmState :=
  pointAddDoubleInvState (pointAddDoubleState6 yst)

def pointAddDoubleFinalState (yst : EvmState) : EvmState :=
  pointAddDoubleSlopeState (pointAddDoubleState7 yst)

private theorem step_pointAddEqualBody (yst : EvmState)
    (out left right : U256)
    (hy : pointAddDoubleYZero (pointAddDoubleState1 yst) = 0)
    (hhi : (fp2InvNorm (pointAddDoubleState6 yst) 2432).1.toNat <
      2 ^ 128) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) (pointAddDoubleState0 yst)
      (.block pointAddEqualBody) (pointAddInitialEnv out left right)
      (pointAddDoubleFinalState yst) .normal := by
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddDoubleState0 yst) pointAddEqualBody
      (pointAddInitialEnv out left right)
      (pointAddDoubleFinalState yst) .normal := by
    rw [pointAddEqualBody_eq]
    exact Step.seqCons
      (step_pointAddDoubleYSum (pointAddDoubleState0 yst) out left right)
      (Step.seqCons
        (step_pointAddDoubleYNonzero (pointAddDoubleState1 yst)
          out left right hy)
        (Step.seqCons
          (step_pointAddDoubleSquare (pointAddDoubleState2 yst)
            out left right)
          (Step.seqCons
            (step_pointAddDoubleNum2 (pointAddDoubleState3 yst)
              out left right)
            (Step.seqCons
              (step_pointAddDoubleNum3 (pointAddDoubleState4 yst)
                out left right)
              (Step.seqCons
                (step_pointAddDoubleDenominator (pointAddDoubleState5 yst)
                  out left right)
                (Step.seqCons
                  (step_pointAddDoubleInverse (pointAddDoubleState6 yst)
                    out left right hhi)
                  (Step.seqCons
                    (step_pointAddDoubleSlope (pointAddDoubleState7 yst)
                      out left right)
                    Step.seqNil)))))))
  have hblock := Step.block (D := Challenge.EvmProof.modexpExec.toDialect)
    (body := pointAddEqualBody) hseq
  simpa [restore, pointAddInitialEnv] using hblock

theorem step_pointAddEqualRun (yst : EvmState) (out left right : U256)
    (heq : pointAddEqValue yst ≠ 0)
    (hy : pointAddDoubleYZero (pointAddDoubleState1 yst) = 0)
    (hhi : (fp2InvNorm (pointAddDoubleState6 yst) 2432).1.toNat <
      2 ^ 128) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddStmt5
      (pointAddInitialEnv out left right)
      (pointAddDoubleFinalState yst) .normal := by
  rw [pointAddStmt5_eq]
  exact Step.ifTrue (step_pointAddEqualCondition yst out left right) heq
    (step_pointAddEqualBody yst out left right hy hhi)

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
