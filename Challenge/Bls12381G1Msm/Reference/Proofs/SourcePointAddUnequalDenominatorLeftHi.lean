import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDenominatorLeftLoMemory

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
open YulSemantics YulSemantics.EVM

theorem step_pointAddUnequalDenominatorLeftHi (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorLeftLoEnv yst out left right)
      (pointAddUnequalDenominatorState2 yst out left right)
      pointAddUnequalDenominatorRawStmt1
      (pointAddUnequalDenominatorLeftHiEnv yst out left right)
      (pointAddUnequalDenominatorState4 yst out left right) .normal := by
  rw [pointAddUnequalDenominatorRawStmt1_eq]
  have hexpr : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorLeftLoEnv yst out left right)
      (pointAddUnequalDenominatorState2 yst out left right)
      (.builtin .mload [.builtin .mload [.lit (.number 1568)]])
      (.vals [pointAddUnequalLeftXHi yst out left right]
        (pointAddUnequalDenominatorState4 yst out left right)) := by
    simpa [pointAddUnequalLeftXHi, pointAddUnequalLeftPtr,
      pointAddUnequalDenominatorState2_memory,
      pointAddUnequalNumeratorInputsState_memory,
      pointAddUnequalDenominatorState3,
      pointAddUnequalDenominatorState4] using
      (step_nestedLoad (funs := [] :: [] :: pointAddBodyFuns)
        (V := pointAddUnequalDenominatorLeftLoEnv yst out left right)
        (pointAddUnequalDenominatorState2 yst out left right) 1568)
  exact Step.letVal hexpr rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
