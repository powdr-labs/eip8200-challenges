import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDenominatorRepair
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceAssignVar

set_option warningAsError true

/-! Complete unequal denominator subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalDenominatorHighOutEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalDenominatorSelectedEnv yst out left right) "\x00130"
    (pointAddUnequalDenominatorResult yst out left right).1

def pointAddUnequalDenominatorWorkEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalDenominatorHighOutEnv yst out left right) "\x00131"
    (pointAddUnequalDenominatorResult yst out left right).2

private theorem selected_hi (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddUnequalDenominatorSelectedEnv yst out left right) "fc0_74" =
      some (pointAddUnequalDenominatorResult yst out left right).1 := by rfl

private theorem selected_lo (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddUnequalDenominatorSelectedEnv yst out left right) "fc0_75" =
      some (pointAddUnequalDenominatorResult yst out left right).2 := by rfl

private theorem step_outHi (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorSelectedEnv yst out left right)
      (pointAddUnequalDenominatorInputsState yst out left right)
      pointAddUnequalDenominatorOutHiStmt
      (pointAddUnequalDenominatorHighOutEnv yst out left right)
      (pointAddUnequalDenominatorInputsState yst out left right) .normal := by
  rw [pointAddUnequalDenominatorOutHiStmt_eq]
  exact step_assignVar (selected_hi yst out left right)

private theorem highOut_lo (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddUnequalDenominatorHighOutEnv yst out left right) "fc0_75" =
      some (pointAddUnequalDenominatorResult yst out left right).2 := by
  rw [pointAddUnequalDenominatorHighOutEnv,
    venv_get_set_ne _ _ _ _ (by decide)]
  exact selected_lo yst out left right

private theorem step_outLo (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorHighOutEnv yst out left right)
      (pointAddUnequalDenominatorInputsState yst out left right)
      pointAddUnequalDenominatorOutLoStmt
      (pointAddUnequalDenominatorWorkEnv yst out left right)
      (pointAddUnequalDenominatorInputsState yst out left right) .normal := by
  rw [pointAddUnequalDenominatorOutLoStmt_eq]
  exact step_assignVar (highOut_lo yst out left right)

def pointAddUnequalDenominatorEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (pointAddUnequalDenominatorInitialEnv yst out left right)
    (pointAddUnequalDenominatorWorkEnv yst out left right)

theorem step_pointAddUnequalDenominatorInit (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalNumeratorEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right)
      pointAddUnequalDenominatorInitStmt
      (pointAddUnequalDenominatorInitialEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right) .normal := by
  rw [pointAddUnequalDenominatorInitStmt_eq]
  simpa [pointAddUnequalDenominatorInitialEnv] using
    (Step.letZero (D := Challenge.EvmProof.modexpExec.toDialect)
      (funs := pointAddBodyFuns)
      (V := pointAddUnequalNumeratorEnv yst out left right)
      (st := pointAddUnequalNumeratorInputsState yst out left right)
      (vars := ["\x00130", "\x00131"]))

theorem step_pointAddUnequalDenominatorBlock (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalDenominatorInitialEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right)
      pointAddUnequalDenominatorStmt
      (pointAddUnequalDenominatorEnv yst out left right)
      (pointAddUnequalDenominatorInputsState yst out left right) .normal := by
  have hbody : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorInitialEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right)
      pointAddUnequalDenominatorBody
      (pointAddUnequalDenominatorWorkEnv yst out left right)
      (pointAddUnequalDenominatorInputsState yst out left right) .normal := by
    rw [pointAddUnequalDenominatorBody_eq]
    exact Step.seqCons (step_pointAddUnequalDenominatorRawDecl yst out left right)
      (Step.seqCons (step_pointAddUnequalDenominatorRawBlock yst out left right)
        (Step.seqCons (step_pointAddUnequalDenominatorRepair yst out left right)
          (Step.seqCons (step_outHi yst out left right)
            (Step.seqCons (step_outLo yst out left right) Step.seqNil))))
  rw [pointAddUnequalDenominatorStmt_eq, pointAddUnequalDenominatorEnv]
  exact Step.block hbody

theorem step_pointAddUnequalDenominator (yst : EvmState)
    (out left right : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalNumeratorEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right)
      [pointAddUnequalDenominatorInitStmt, pointAddUnequalDenominatorStmt]
      (pointAddUnequalDenominatorEnv yst out left right)
      (pointAddUnequalDenominatorInputsState yst out left right) .normal :=
  Step.seqCons (step_pointAddUnequalDenominatorInit yst out left right)
    (Step.seqCons (step_pointAddUnequalDenominatorBlock yst out left right)
      Step.seqNil)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
