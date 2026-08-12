import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddRun
import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddYZero

set_option warningAsError true

/-! Complete terminating executions of the frozen G2MSM `pointAdd`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem appendNormalExceptional {funs V st pre Vmid stmid suffix Vend
    stend outcome}
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

private theorem pointAddBody_exceptionalSplit : pointAddBody =
    [pointAddStmt0, pointAddStmt1, pointAddStmt2] ++
    ([pointAddStmt3, pointAddStmt4] ++
      ([pointAddStmt5, pointAddStmt6] ++ pointAddPostBody)) := by rfl

private theorem step_pointAddBodyLeftIdentity (yst : EvmState)
    (out left right : U256)
    (hinfinity : pointZeroValue (pointAddLeftPointerState yst out left right)
      (pointAddLeftPointer yst out left right) ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddBody
      (pointAddInitialEnv out left right)
      (pointAddLeftFinalState yst out left right) .leave := by
  have htail : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right)
      ([pointAddStmt3, pointAddStmt4] ++
        ([pointAddStmt5, pointAddStmt6] ++ pointAddPostBody))
      (pointAddInitialEnv out left right)
      (pointAddLeftFinalState yst out left right) .leave :=
    Step.seqStop (step_pointAddLeftInfinity yst out left right hinfinity)
      (by decide)
  have hrun := appendNormalExceptional
    (step_pointAddPrefix yst out left right) htail
  rw [pointAddBody_exceptionalSplit]
  exact hrun

private theorem step_pointAddBodyRightIdentity (yst : EvmState)
    (out left right : U256)
    (hleft : pointZeroValue (pointAddLeftPointerState yst out left right)
      (pointAddLeftPointer yst out left right) = 0)
    (hright : pointZeroValue (pointAddRightPointerState yst out left right)
      (pointAddRightPointer yst out left right) ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddBody
      (pointAddInitialEnv out left right)
      (pointAddRightFinalState yst out left right) .leave := by
  have htail : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right)
      ([pointAddStmt3, pointAddStmt4] ++
        ([pointAddStmt5, pointAddStmt6] ++ pointAddPostBody))
      (pointAddInitialEnv out left right)
      (pointAddRightFinalState yst out left right) .leave :=
    Step.seqCons (step_pointAddLeftFinite yst out left right hleft)
      (Step.seqStop (step_pointAddRightInfinity yst out left right hright)
        (by decide))
  have hrun := appendNormalExceptional
    (step_pointAddPrefix yst out left right) htail
  rw [pointAddBody_exceptionalSplit]
  exact hrun

private theorem step_pointAddEqualYZeroRun (yst : EvmState)
    (out left right : U256) (heq : pointAddEqValue yst ≠ 0)
    (hy : pointAddDoubleYZero (pointAddDoubleState1 yst) ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddStmt5
      (pointAddInitialEnv out left right)
      (pointAddYZeroFinalState (pointAddDoubleState1 yst)) .leave := by
  have hbodySeq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddDoubleState0 yst) pointAddEqualBody
      (pointAddInitialEnv out left right)
      (pointAddYZeroFinalState (pointAddDoubleState1 yst)) .leave := by
    rw [pointAddEqualBody_eq]
    exact Step.seqCons
      (step_pointAddDoubleYSum (pointAddDoubleState0 yst) out left right)
      (Step.seqStop
        (step_pointAddDoubleYZero (pointAddDoubleState1 yst)
          out left right hy)
        (by decide))
  have hbodyBlock := Step.block
    (D := Challenge.EvmProof.modexpExec.toDialect)
    (body := pointAddEqualBody) hbodySeq
  have hbody : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddDoubleState0 yst) (.block pointAddEqualBody)
      (pointAddInitialEnv out left right)
      (pointAddYZeroFinalState (pointAddDoubleState1 yst)) .leave := by
    simpa [restore, pointAddInitialEnv] using hbodyBlock
  rw [pointAddStmt5_eq]
  exact Step.ifTrue (step_pointAddEqualCondition yst out left right) heq
    (by simpa [pointAddDoubleState0] using hbody)

private theorem step_pointAddBodyYZero (yst : EvmState)
    (out left right : U256)
    (hleft : pointZeroValue (pointAddLeftPointerState yst out left right)
      (pointAddLeftPointer yst out left right) = 0)
    (hright : pointZeroValue (pointAddRightPointerState yst out left right)
      (pointAddRightPointer yst out left right) = 0)
    (heq : pointAddEqValue (pointAddFiniteStart yst out left right) ≠ 0)
    (hy : pointAddDoubleYZero
      (pointAddDoubleState1 (pointAddFiniteStart yst out left right)) ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddBody
      (pointAddInitialEnv out left right)
      (pointAddYZeroFinalState
        (pointAddDoubleState1 (pointAddFiniteStart yst out left right)))
      .leave := by
  have htail : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right)
      ([pointAddStmt3, pointAddStmt4] ++
        ([pointAddStmt5, pointAddStmt6] ++ pointAddPostBody))
      (pointAddInitialEnv out left right)
      (pointAddYZeroFinalState
        (pointAddDoubleState1 (pointAddFiniteStart yst out left right)))
      .leave :=
    Step.seqCons (step_pointAddLeftFinite yst out left right hleft)
      (Step.seqCons (step_pointAddRightFinite yst out left right hright)
        (Step.seqStop (step_pointAddEqualYZeroRun
          (pointAddFiniteStart yst out left right) out left right heq hy)
          (by decide)))
  have hrun := appendNormalExceptional
    (step_pointAddPrefix yst out left right) htail
  rw [pointAddBody_exceptionalSplit]
  exact hrun

theorem step_pointAddLeftIdentity (yst : EvmState) (out left right : U256)
    (hinfinity : pointZeroValue (pointAddLeftPointerState yst out left right)
      (pointAddLeftPointer yst out left right) ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddFuns
      (pointAddInitialEnv out left right) yst (.block pointAddBody)
      (pointAddInitialEnv out left right)
      (pointAddLeftFinalState yst out left right) .leave := by
  have hseq := step_pointAddBodyLeftIdentity yst out left right hinfinity
  rw [← pointAddBodyFuns_eq] at hseq
  have hblock := Step.block (D := Challenge.EvmProof.modexpExec.toDialect) hseq
  simpa [restore, pointAddInitialEnv] using hblock

theorem step_pointAddRightIdentity (yst : EvmState) (out left right : U256)
    (hleft : pointZeroValue (pointAddLeftPointerState yst out left right)
      (pointAddLeftPointer yst out left right) = 0)
    (hright : pointZeroValue (pointAddRightPointerState yst out left right)
      (pointAddRightPointer yst out left right) ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddFuns
      (pointAddInitialEnv out left right) yst (.block pointAddBody)
      (pointAddInitialEnv out left right)
      (pointAddRightFinalState yst out left right) .leave := by
  have hseq := step_pointAddBodyRightIdentity yst out left right hleft hright
  rw [← pointAddBodyFuns_eq] at hseq
  have hblock := Step.block (D := Challenge.EvmProof.modexpExec.toDialect) hseq
  simpa [restore, pointAddInitialEnv] using hblock

theorem step_pointAddYZero (yst : EvmState) (out left right : U256)
    (hleft : pointZeroValue (pointAddLeftPointerState yst out left right)
      (pointAddLeftPointer yst out left right) = 0)
    (hright : pointZeroValue (pointAddRightPointerState yst out left right)
      (pointAddRightPointer yst out left right) = 0)
    (heq : pointAddEqValue (pointAddFiniteStart yst out left right) ≠ 0)
    (hy : pointAddDoubleYZero
      (pointAddDoubleState1 (pointAddFiniteStart yst out left right)) ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddFuns
      (pointAddInitialEnv out left right) yst (.block pointAddBody)
      (pointAddInitialEnv out left right)
      (pointAddYZeroFinalState
        (pointAddDoubleState1 (pointAddFiniteStart yst out left right)))
      .leave := by
  have hseq := step_pointAddBodyYZero yst out left right hleft hright heq hy
  rw [← pointAddBodyFuns_eq] at hseq
  have hblock := Step.block (D := Challenge.EvmProof.modexpExec.toDialect) hseq
  simpa [restore, pointAddInitialEnv] using hblock

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
