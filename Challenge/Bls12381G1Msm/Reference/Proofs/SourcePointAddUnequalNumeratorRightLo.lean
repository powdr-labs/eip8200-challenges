import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalNumeratorLeftHiMemory

set_option warningAsError true

/-! Third opaque unequal-numerator input load. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_pointAddUnequalNumeratorRightLo (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorLeftHiEnv yst out left right)
      (pointAddUnequalNumeratorState4 yst out left right)
      pointAddUnequalNumeratorRawStmt2
      (pointAddUnequalNumeratorRightLoEnv yst out left right)
      (pointAddUnequalNumeratorState6 yst out left right) .normal := by
  rw [pointAddUnequalNumeratorRawStmt2_eq]
  have hexpr : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorLeftHiEnv yst out left right)
      (pointAddUnequalNumeratorState4 yst out left right)
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1600)], .lit (.number 96)]])
      (.vals [pointAddUnequalRightYLo yst out left right]
        (pointAddUnequalNumeratorState6 yst out left right)) := by
    simpa [pointAddUnequalRightYLo, pointAddUnequalRightPtr,
      pointAddUnequalNumeratorState5, pointAddUnequalNumeratorState6] using
      (step_nestedLoadAdd (funs := [] :: [] :: pointAddBodyFuns)
        (V := pointAddUnequalNumeratorLeftHiEnv yst out left right)
        (pointAddUnequalNumeratorState4 yst out left right) 1600 96)
  exact Step.letVal hexpr rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
