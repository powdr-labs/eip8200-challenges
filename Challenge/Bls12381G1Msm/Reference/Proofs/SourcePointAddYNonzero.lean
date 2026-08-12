import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddYZeroBranch

set_option warningAsError true

/-! Normal exit from the equal-x exceptional classifier into doubling. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddYNonzeroEnv (yst : EvmState) (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (pointAddInitialEnv out left right) (pointAddYSumEnv yst out left right)

private theorem step_pointAddYZeroSkip {funs} (yst : EvmState)
    (out left right : U256)
    (hzero : pointAddYZeroValue yst out left right = 0)
    (hlookup : lookupFun funs "\x002" = some (fpZeroDecl, sourceFuns)) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddYSumEnv yst out left right) (pointAddYSumState yst out left right)
      pointAddYZeroStmt (pointAddYSumEnv yst out left right)
      (pointAddYSumState yst out left right) .normal := by
  rw [pointAddYZeroStmt_eq]
  exact Step.ifFalse
    (step_pointAddYZero_of_lookup yst out left right hlookup) hzero

theorem step_pointAddYNonzero (yst : EvmState) (out left right : U256)
    (hzero : pointAddYZeroValue yst out left right = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) (pointAddXEqState yst out left right)
      pointAddXEqExceptionalStmt (pointAddYNonzeroEnv yst out left right)
      (pointAddYSumState yst out left right) .normal := by
  let nestedFuns :=
    hoist Challenge.EvmProof.modexpExec.toDialect pointAddXEqExceptionalBody ::
      pointAddBodyFuns
  have hsum : ExecStmt Challenge.EvmProof.modexpExec.toDialect nestedFuns
      (pointAddInitialEnv out left right) (pointAddXEqState yst out left right)
      pointAddYSumStmt (pointAddYSumEnv yst out left right)
      (pointAddYSumState yst out left right) .normal :=
    step_pointAddYSumStmt_of_lookup yst out left right (by rfl)
  have hskip : ExecStmt Challenge.EvmProof.modexpExec.toDialect nestedFuns
      (pointAddYSumEnv yst out left right) (pointAddYSumState yst out left right)
      pointAddYZeroStmt (pointAddYSumEnv yst out left right)
      (pointAddYSumState yst out left right) .normal :=
    step_pointAddYZeroSkip yst out left right hzero (by rfl)
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect nestedFuns
      (pointAddInitialEnv out left right) (pointAddXEqState yst out left right)
      pointAddXEqExceptionalBody (pointAddYSumEnv yst out left right)
      (pointAddYSumState yst out left right) .normal := by
    rw [pointAddXEqExceptionalBody_eq]
    exact Step.seqCons hsum (Step.seqCons hskip Step.seqNil)
  rw [pointAddXEqExceptionalStmt_eq]
  exact Step.block hseq

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
