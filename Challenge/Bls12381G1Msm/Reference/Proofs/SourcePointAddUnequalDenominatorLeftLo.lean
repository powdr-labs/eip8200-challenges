import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDenominatorInputsDefs

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
open YulSemantics YulSemantics.EVM

theorem step_pointAddUnequalDenominatorLeftLo (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorRawInitialEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right)
      pointAddUnequalDenominatorRawStmt0
      (pointAddUnequalDenominatorLeftLoEnv yst out left right)
      (pointAddUnequalDenominatorState2 yst out left right) .normal := by
  rw [pointAddUnequalDenominatorRawStmt0_eq]
  have hexpr : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorRawInitialEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right)
      (.builtin .mload [.builtin .add
        [.builtin .mload [.lit (.number 1568)], .lit (.number 32)]])
      (.vals [pointAddUnequalLeftXLo yst out left right]
        (pointAddUnequalDenominatorState2 yst out left right)) := by
    simpa [pointAddUnequalLeftXLo, pointAddUnequalLeftPtr,
      pointAddUnequalNumeratorInputsState_memory,
      pointAddUnequalDenominatorState1, pointAddUnequalDenominatorState2] using
      (step_nestedLoadAdd (funs := [] :: [] :: pointAddBodyFuns)
        (V := pointAddUnequalDenominatorRawInitialEnv yst out left right)
        (pointAddUnequalNumeratorInputsState yst out left right) 1568 32)
  exact Step.letVal hexpr rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
