import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalYSubBridge
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalPostludeBridge

set_option warningAsError true

/-! Existential firebreak for the final unequal y subtraction and output stores. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalTailCode : Block Op :=
  pointAddUnequalYSubStmt :: pointAddUnequalPostlude

theorem step_pointAddUnequalTail (yst : EvmState) (out left right : U256) :
    ∃ Vend stend,
      ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
        (pointAddUnequalYMulEnv yst out left right)
        (pointAddUnequalYMulState yst out left right)
        pointAddUnequalTailCode Vend stend .normal := by
  refine ⟨pointAddUnequalFinalEnv yst out left right,
    pointAddUnequalFinalState yst out left right, ?_⟩
  have hpost : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddUnequalYSubConcreteEnv yst out left right)
      (pointAddUnequalYSubConcreteState yst out left right)
      pointAddUnequalPostlude (pointAddUnequalFinalEnv yst out left right)
      (pointAddUnequalFinalState yst out left right) .normal := by
    simpa only [pointAddUnequalPostContext_env,
      pointAddUnequalPostContext_state, pointAddUnequalFinalEnv,
      pointAddUnequalFinalState] using
        (step_pointAddUnequalPostlude yst out left right)
  rw [pointAddUnequalTailCode]
  exact Step.seqCons (step_pointAddUnequalYSubStmt yst out left right)
    hpost

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
