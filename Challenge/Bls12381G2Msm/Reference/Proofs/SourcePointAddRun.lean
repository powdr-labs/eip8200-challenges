import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddFiniteRun

set_option warningAsError true

/-! Complete normal finite executions of the frozen G2MSM `pointAdd`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddFiniteStart (yst : EvmState) (out left right : U256) : EvmState :=
  pointAddRightInfinityState yst out left right

private theorem appendNormal {funs V st pre Vmid stmid suffix Vend stend outcome}
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

private theorem pointAddBody_split : pointAddBody =
    [pointAddStmt0, pointAddStmt1, pointAddStmt2] ++
    [pointAddStmt3, pointAddStmt4] ++
    ([pointAddStmt5, pointAddStmt6] ++ pointAddPostBody) := by rfl

theorem step_pointAddBodyDouble (yst : EvmState) (out left right : U256)
    (hleft : pointZeroValue (pointAddLeftPointerState yst out left right)
      (pointAddLeftPointer yst out left right) = 0)
    (hright : pointZeroValue (pointAddRightPointerState yst out left right)
      (pointAddRightPointer yst out left right) = 0)
    (heq : pointAddEqValue (pointAddFiniteStart yst out left right) ≠ 0)
    (hy : pointAddDoubleYZero
      (pointAddDoubleState1 (pointAddFiniteStart yst out left right)) = 0)
    (hhi : (fp2InvNorm
      (pointAddDoubleState6 (pointAddFiniteStart yst out left right))
      2432).1.toNat < 2 ^ 128)
    (heq2 : pointAddEqValue
      (pointAddDoubleFinalState (pointAddFiniteStart yst out left right)) ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddBody
      (pointAddInitialEnv out left right)
      (pointAddFiniteDoubleFinal (pointAddFiniteStart yst out left right))
      .normal := by
  have hmiddle : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right)
      [pointAddStmt3, pointAddStmt4]
      (pointAddInitialEnv out left right)
      (pointAddFiniteStart yst out left right) .normal :=
    Step.seqCons (step_pointAddLeftFinite yst out left right hleft)
      (Step.seqCons (step_pointAddRightFinite yst out left right hright)
        Step.seqNil)
  have hfinite := step_pointAddFiniteDouble
    (pointAddFiniteStart yst out left right) out left right heq hy hhi heq2
  have hrun := appendNormal (step_pointAddPrefix yst out left right)
    (appendNormal hmiddle hfinite)
  rw [pointAddBody_split]
  simpa only [List.append_assoc] using hrun

theorem step_pointAddBodyUnequal (yst : EvmState) (out left right : U256)
    (hleft : pointZeroValue (pointAddLeftPointerState yst out left right)
      (pointAddLeftPointer yst out left right) = 0)
    (hright : pointZeroValue (pointAddRightPointerState yst out left right)
      (pointAddRightPointer yst out left right) = 0)
    (heq1 : pointAddEqValue (pointAddFiniteStart yst out left right) = 0)
    (heq2 : pointAddEqValue (pointAddUnequalAfterEqualSkip
      (pointAddFiniteStart yst out left right)) = 0)
    (hhi : (fp2InvNorm (pointAddUnequalState2
      (pointAddUnequalAfterEqualSkip
        (pointAddFiniteStart yst out left right))) 2432).1.toNat < 2 ^ 128) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddBody
      (pointAddInitialEnv out left right)
      (pointAddFiniteUnequalFinal (pointAddFiniteStart yst out left right))
      .normal := by
  have hmiddle : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right)
      [pointAddStmt3, pointAddStmt4]
      (pointAddInitialEnv out left right)
      (pointAddFiniteStart yst out left right) .normal :=
    Step.seqCons (step_pointAddLeftFinite yst out left right hleft)
      (Step.seqCons (step_pointAddRightFinite yst out left right hright)
        Step.seqNil)
  have hfinite := step_pointAddFiniteUnequal
    (pointAddFiniteStart yst out left right)
    out left right heq1 heq2 hhi
  have hrun := appendNormal (step_pointAddPrefix yst out left right)
    (appendNormal hmiddle hfinite)
  rw [pointAddBody_split]
  simpa only [List.append_assoc] using hrun

theorem step_pointAddDouble (yst : EvmState) (out left right : U256)
    (hleft : pointZeroValue (pointAddLeftPointerState yst out left right)
      (pointAddLeftPointer yst out left right) = 0)
    (hright : pointZeroValue (pointAddRightPointerState yst out left right)
      (pointAddRightPointer yst out left right) = 0)
    (heq : pointAddEqValue (pointAddFiniteStart yst out left right) ≠ 0)
    (hy : pointAddDoubleYZero
      (pointAddDoubleState1 (pointAddFiniteStart yst out left right)) = 0)
    (hhi : (fp2InvNorm
      (pointAddDoubleState6 (pointAddFiniteStart yst out left right))
      2432).1.toNat < 2 ^ 128)
    (heq2 : pointAddEqValue
      (pointAddDoubleFinalState (pointAddFiniteStart yst out left right)) ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddFuns
      (pointAddInitialEnv out left right) yst (.block pointAddBody)
      (pointAddInitialEnv out left right)
      (pointAddFiniteDoubleFinal (pointAddFiniteStart yst out left right))
      .normal := by
  have hseq := step_pointAddBodyDouble yst out left right
    hleft hright heq hy hhi heq2
  rw [← pointAddBodyFuns_eq] at hseq
  have hblock := Step.block (D := Challenge.EvmProof.modexpExec.toDialect) hseq
  simpa [restore, pointAddInitialEnv] using hblock

theorem step_pointAddUnequal (yst : EvmState) (out left right : U256)
    (hleft : pointZeroValue (pointAddLeftPointerState yst out left right)
      (pointAddLeftPointer yst out left right) = 0)
    (hright : pointZeroValue (pointAddRightPointerState yst out left right)
      (pointAddRightPointer yst out left right) = 0)
    (heq1 : pointAddEqValue (pointAddFiniteStart yst out left right) = 0)
    (heq2 : pointAddEqValue (pointAddUnequalAfterEqualSkip
      (pointAddFiniteStart yst out left right)) = 0)
    (hhi : (fp2InvNorm (pointAddUnequalState2
      (pointAddUnequalAfterEqualSkip
        (pointAddFiniteStart yst out left right))) 2432).1.toNat < 2 ^ 128) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddFuns
      (pointAddInitialEnv out left right) yst (.block pointAddBody)
      (pointAddInitialEnv out left right)
      (pointAddFiniteUnequalFinal (pointAddFiniteStart yst out left right))
      .normal := by
  have hseq := step_pointAddBodyUnequal yst out left right
    hleft hright heq1 heq2 hhi
  rw [← pointAddBodyFuns_eq] at hseq
  have hblock := Step.block (D := Challenge.EvmProof.modexpExec.toDialect) hseq
  simpa [restore, pointAddInitialEnv] using hblock

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
