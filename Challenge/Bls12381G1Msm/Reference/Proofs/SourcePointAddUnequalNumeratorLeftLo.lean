import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalNumeratorInputsDefs

set_option warningAsError true

/-! First opaque unequal-numerator input load. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_pointAddUnequalNumeratorLeftLo (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorRawInitialEnv out left right)
      (pointAddXEqState yst out left right)
      pointAddUnequalNumeratorRawStmt0
      (pointAddUnequalNumeratorLeftLoEnv yst out left right)
      (pointAddUnequalNumeratorState2 yst out left right) .normal := by
  rw [pointAddUnequalNumeratorRawStmt0_eq]
  have hexpr : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorRawInitialEnv out left right)
      (pointAddXEqState yst out left right)
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 96)]])
      (.vals [pointAddUnequalLeftYLo yst out left right]
        (pointAddUnequalNumeratorState2 yst out left right)) := by
    simpa [pointAddUnequalLeftYLo, pointAddUnequalLeftPtr,
      pointAddUnequalNumeratorState1, pointAddUnequalNumeratorState2] using
      (step_nestedLoadAdd (funs := [] :: [] :: pointAddBodyFuns)
        (V := pointAddUnequalNumeratorRawInitialEnv out left right)
        (pointAddXEqState yst out left right) 1568 96)
  exact Step.letVal hexpr rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
