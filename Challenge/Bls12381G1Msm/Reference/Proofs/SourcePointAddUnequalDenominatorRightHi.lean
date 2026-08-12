import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDenominatorRightLoMemory

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
open YulSemantics YulSemantics.EVM

theorem step_pointAddUnequalDenominatorRightHi (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorRightLoEnv yst out left right)
      (pointAddUnequalDenominatorState6 yst out left right)
      pointAddUnequalDenominatorRawStmt3
      (pointAddUnequalDenominatorInputsEnv yst out left right)
      (pointAddUnequalDenominatorInputsState yst out left right) .normal := by
  rw [pointAddUnequalDenominatorRawStmt3_eq]
  have hexpr : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorRightLoEnv yst out left right)
      (pointAddUnequalDenominatorState6 yst out left right)
      (.builtin .mload [.builtin .mload [.lit (.number 1600)]])
      (.vals [pointAddUnequalRightXHi yst out left right]
        (pointAddUnequalDenominatorInputsState yst out left right)) := by
    simpa [pointAddUnequalRightXHi, pointAddUnequalRightPtr,
      pointAddUnequalDenominatorState6_memory,
      pointAddUnequalNumeratorInputsState_memory,
      pointAddUnequalDenominatorState7,
      pointAddUnequalDenominatorInputsState] using
      (step_nestedLoad (funs := [] :: [] :: pointAddBodyFuns)
        (V := pointAddUnequalDenominatorRightLoEnv yst out left right)
        (pointAddUnequalDenominatorState6 yst out left right) 1600)
  exact Step.letVal hexpr rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
