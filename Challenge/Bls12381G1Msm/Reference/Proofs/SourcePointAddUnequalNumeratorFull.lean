import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalNumeratorRepair
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceAssignVar

set_option warningAsError true

/-! Complete unequal numerator subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalNumeratorHighOutEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalNumeratorSelectedEnv yst out left right) "\x00128"
    (pointAddUnequalNumeratorResult yst out left right).1

def pointAddUnequalNumeratorWorkEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalNumeratorHighOutEnv yst out left right) "\x00129"
    (pointAddUnequalNumeratorResult yst out left right).2

private theorem selected_hi (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddUnequalNumeratorSelectedEnv yst out left right) "fc0_67" =
      some (pointAddUnequalNumeratorResult yst out left right).1 := by rfl

private theorem selected_lo (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddUnequalNumeratorSelectedEnv yst out left right) "fc0_68" =
      some (pointAddUnequalNumeratorResult yst out left right).2 := by rfl

private theorem step_outHi (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorSelectedEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right)
      pointAddUnequalNumeratorOutHiStmt
      (pointAddUnequalNumeratorHighOutEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right) .normal := by
  rw [pointAddUnequalNumeratorOutHiStmt_eq]
  exact step_assignVar (selected_hi yst out left right)

private theorem highOut_lo (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddUnequalNumeratorHighOutEnv yst out left right) "fc0_68" =
      some (pointAddUnequalNumeratorResult yst out left right).2 := by
  rw [pointAddUnequalNumeratorHighOutEnv,
    venv_get_set_ne _ _ _ _ (by decide)]
  exact selected_lo yst out left right

private theorem step_outLo (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorHighOutEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right)
      pointAddUnequalNumeratorOutLoStmt
      (pointAddUnequalNumeratorWorkEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right) .normal := by
  rw [pointAddUnequalNumeratorOutLoStmt_eq]
  exact step_assignVar (highOut_lo yst out left right)

def pointAddUnequalNumeratorEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (pointAddUnequalNumeratorInitialEnv out left right)
    (pointAddUnequalNumeratorWorkEnv yst out left right)

theorem step_pointAddUnequalNumerator (yst : EvmState)
    (out left right : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) (pointAddXEqState yst out left right)
      [pointAddUnequalNumeratorInitStmt, pointAddUnequalNumeratorStmt]
      (pointAddUnequalNumeratorEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right) .normal := by
  have hbody : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorInitialEnv out left right)
      (pointAddXEqState yst out left right) pointAddUnequalNumeratorBody
      (pointAddUnequalNumeratorWorkEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right) .normal := by
    rw [pointAddUnequalNumeratorBody_eq]
    exact Step.seqCons (step_pointAddUnequalNumeratorRawDecl yst out left right)
      (Step.seqCons (step_pointAddUnequalNumeratorRawBlock yst out left right)
        (Step.seqCons (step_pointAddUnequalNumeratorRepair yst out left right)
          (Step.seqCons (step_outHi yst out left right)
            (Step.seqCons (step_outLo yst out left right) Step.seqNil))))
  have hblock : ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalNumeratorInitialEnv out left right)
      (pointAddXEqState yst out left right) pointAddUnequalNumeratorStmt
      (pointAddUnequalNumeratorEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right) .normal := by
    rw [pointAddUnequalNumeratorStmt_eq, pointAddUnequalNumeratorEnv]
    exact Step.block hbody
  exact Step.seqCons (step_pointAddUnequalNumeratorInit yst out left right)
    (Step.seqCons hblock Step.seqNil)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
