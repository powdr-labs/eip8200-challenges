import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalNumeratorRightLoMemory

set_option warningAsError true

/-! Fourth opaque unequal-numerator input load. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_pointAddUnequalNumeratorRightHi (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorRightLoEnv yst out left right)
      (pointAddUnequalNumeratorState6 yst out left right)
      pointAddUnequalNumeratorRawStmt3
      (pointAddUnequalNumeratorInputsEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right) .normal := by
  rw [pointAddUnequalNumeratorRawStmt3_eq]
  have hexpr : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorRightLoEnv yst out left right)
      (pointAddUnequalNumeratorState6 yst out left right)
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1600)], .lit (.number 64)]])
      (.vals [pointAddUnequalRightYHi yst out left right]
        (pointAddUnequalNumeratorInputsState yst out left right)) := by
    simpa [pointAddUnequalRightYHi, pointAddUnequalRightPtr,
      pointAddUnequalNumeratorState7, pointAddUnequalNumeratorInputsState] using
      (step_nestedLoadAdd (funs := [] :: [] :: pointAddBodyFuns)
        (V := pointAddUnequalNumeratorRightLoEnv yst out left right)
        (pointAddUnequalNumeratorState6 yst out left right) 1600 64)
  exact Step.letVal hexpr rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
