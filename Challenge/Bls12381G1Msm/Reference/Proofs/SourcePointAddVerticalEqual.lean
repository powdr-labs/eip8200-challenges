import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddYZeroBranch
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddYSumCall
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddXEq
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFunEnvInsert

set_option warningAsError true

/-! Complete equal-x vertical branch of the finite point-add condition. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_pointAddVerticalEqual (yst : EvmState)
    (out left right : U256)
    (hxeq : pointAddXEqValue yst out left right ≠ 0)
    (hzero : pointAddYZeroValue yst out left right ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) (pointAddFiniteState yst out left right)
      pointAddStmt5 (pointAddInitialEnv out left right)
      (pointAddYZeroState yst out left right) .leave := by
  have hsum : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddXEqState yst out left right) pointAddYSumStmt
      (pointAddYSumEnv yst out left right)
      (pointAddYSumState yst out left right) .normal :=
    step_pointAddYSumStmt_of_lookup yst out left right (by rfl)
  have hzeroBranch : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddYSumEnv yst out left right)
      (pointAddYSumState yst out left right) pointAddYZeroStmt
      (pointAddYSumEnv yst out left right)
      (pointAddYZeroState yst out left right) .leave := by
    simpa [pointAddBodyFuns] using
      (step_funEnvInsert
        (step_funEnvInsert
          (step_pointAddYZeroBranch yst out left right hzero)
          (FunEnvInsertEmpty.here pointAddBodyFuns))
        (FunEnvInsertEmpty.underScope []
          (FunEnvInsertEmpty.here pointAddBodyFuns)))
  have hexceptionalBody : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddXEqState yst out left right) pointAddXEqExceptionalBody
      (pointAddYSumEnv yst out left right)
      (pointAddYZeroState yst out left right) .leave := by
    rw [pointAddXEqExceptionalBody_eq]
    exact Step.seqCons hsum (Step.seqStop hzeroBranch (by decide))
  have hexceptional : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddXEqState yst out left right) pointAddXEqExceptionalStmt
      (pointAddInitialEnv out left right)
      (pointAddYZeroState yst out left right) .leave := by
    rw [pointAddXEqExceptionalStmt_eq]
    exact Step.block (D := Challenge.EvmProof.modexpExec.toDialect)
      (body := pointAddXEqExceptionalBody)
      hexceptionalBody
  have hmainBody : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddXEqState yst out left right) pointAddXEqMainBody
      (pointAddInitialEnv out left right)
      (pointAddYZeroState yst out left right) .leave := by
    rw [show pointAddXEqMainBody =
      pointAddXEqExceptionalStmt :: pointAddXEqMainBody.drop 1 by rfl]
    exact Step.seqStop hexceptional (by decide)
  have hmain : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddXEqState yst out left right) (.block pointAddXEqBody)
      (pointAddInitialEnv out left right)
      (pointAddYZeroState yst out left right) .leave := by
    rw [pointAddXEqBody_eq]
    have hmainStmt : ExecStmt Challenge.EvmProof.modexpExec.toDialect
        ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
        (pointAddXEqState yst out left right) pointAddXEqMainStmt
        (pointAddInitialEnv out left right)
        (pointAddYZeroState yst out left right) .leave := by
      rw [pointAddXEqMainStmt_eq]
      have hblock := Step.block (D := Challenge.EvmProof.modexpExec.toDialect)
        (body := pointAddXEqMainBody)
        hmainBody
      simpa [restore, pointAddInitialEnv] using
        step_funEnvInsert hblock (FunEnvInsertEmpty.here pointAddBodyFuns)
    exact Step.block (D := Challenge.EvmProof.modexpExec.toDialect)
      (body := [pointAddXEqMainStmt, .leave])
      (Step.seqStop hmainStmt (by decide))
  rw [pointAddStmt5_eq]
  exact Step.ifTrue (step_pointAddXEq yst out left right) hxeq hmain

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
