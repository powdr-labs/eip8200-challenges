import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalNumeratorLeftLoMemory

set_option warningAsError true

/-! Second opaque unequal-numerator input load. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_pointAddUnequalNumeratorLeftHi (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorLeftLoEnv yst out left right)
      (pointAddUnequalNumeratorState2 yst out left right)
      pointAddUnequalNumeratorRawStmt1
      (pointAddUnequalNumeratorLeftHiEnv yst out left right)
      (pointAddUnequalNumeratorState4 yst out left right) .normal := by
  rw [pointAddUnequalNumeratorRawStmt1_eq]
  have hexpr : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorLeftLoEnv yst out left right)
      (pointAddUnequalNumeratorState2 yst out left right)
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 64)]])
      (.vals [pointAddUnequalLeftYHi yst out left right]
        (pointAddUnequalNumeratorState4 yst out left right)) := by
    simpa [pointAddUnequalLeftYHi, pointAddUnequalLeftPtr,
      pointAddUnequalNumeratorState3, pointAddUnequalNumeratorState4] using
      (step_nestedLoadAdd (funs := [] :: [] :: pointAddBodyFuns)
        (V := pointAddUnequalNumeratorLeftLoEnv yst out left right)
        (pointAddUnequalNumeratorState2 yst out left right) 1568 64)
  exact Step.letVal hexpr rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
