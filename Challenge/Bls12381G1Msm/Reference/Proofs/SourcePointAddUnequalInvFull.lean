import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalInvRestore
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalInvSequence

set_option warningAsError true

/-! Complete relational endpoint for the inlined unequal inversion block. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_pointAddUnequalInvStmt (yst : EvmState)
    (out left right : U256)
    (hhi : (pointAddUnequalDenominatorResult yst out left right).1.toNat <
      2 ^ 128) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalInvInitialEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right)
      pointAddUnequalInvStmt
      (pointAddUnequalInvOutputEnv yst out left right)
      (pointAddUnequalInvFinalState yst out left right) .normal := by
  rw [pointAddUnequalInvStmt_eq]
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect pointAddUnequalInvBody ::
        pointAddBodyFuns)
      (pointAddUnequalInvInitialEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right)
      pointAddUnequalInvBody
      (pointAddUnequalInvFinalWorkEnv yst out left right)
      (pointAddUnequalInvFinalState yst out left right) .normal := by
    rw [hoist_pointAddUnequalInvBody]
    exact step_pointAddUnequalInvBody yst out left right hhi
  have hblock := Step.block hseq
  rw [restore_pointAddUnequalInvFinalWorkEnv] at hblock
  exact hblock

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
