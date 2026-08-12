import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDenominatorLeftHiMemory

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
open YulSemantics YulSemantics.EVM

theorem step_pointAddUnequalDenominatorRightLo (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorLeftHiEnv yst out left right)
      (pointAddUnequalDenominatorState4 yst out left right)
      pointAddUnequalDenominatorRawStmt2
      (pointAddUnequalDenominatorRightLoEnv yst out left right)
      (pointAddUnequalDenominatorState6 yst out left right) .normal := by
  rw [pointAddUnequalDenominatorRawStmt2_eq]
  have hexpr : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorLeftHiEnv yst out left right)
      (pointAddUnequalDenominatorState4 yst out left right)
      (.builtin .mload [.builtin .add
        [.builtin .mload [.lit (.number 1600)], .lit (.number 32)]])
      (.vals [pointAddUnequalRightXLo yst out left right]
        (pointAddUnequalDenominatorState6 yst out left right)) := by
    simpa [pointAddUnequalRightXLo, pointAddUnequalRightPtr,
      pointAddUnequalDenominatorState4_memory,
      pointAddUnequalNumeratorInputsState_memory,
      pointAddUnequalDenominatorState5,
      pointAddUnequalDenominatorState6] using
      (step_nestedLoadAdd (funs := [] :: [] :: pointAddBodyFuns)
        (V := pointAddUnequalDenominatorLeftHiEnv yst out left right)
        (pointAddUnequalDenominatorState4 yst out left right) 1600 32)
  exact Step.letVal hexpr rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
