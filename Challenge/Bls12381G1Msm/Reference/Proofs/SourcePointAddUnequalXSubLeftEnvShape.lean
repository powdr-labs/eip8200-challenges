import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubLeftSelected

set_option warningAsError true

/-! Opaque local-prefix shape of the selected first-subtraction environment. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem pointAddUnequalXSubLeftSelectedEnv_shape (yst : EvmState)
    (out left right : U256) :
    ∃ localHi localLo,
      pointAddUnequalXSubLeftSelectedEnv yst out left right =
        [("fc0_81", localHi), ("fc0_82", localLo)] ++
          pointAddUnequalX3Env yst out left right := by
  by_cases h : pointAddUnequalXSubLeftRepairValue yst out left right = 0
  · exact ⟨(pointAddUnequalXSubLeftRaw yst out left right).1,
      (pointAddUnequalXSubLeftRaw yst out left right).2, by
        rw [pointAddUnequalXSubLeftSelectedEnv, if_pos h]
        rfl⟩
  · exact ⟨(pointAddUnequalXSubLeftRepaired yst out left right).1,
      (pointAddUnequalXSubLeftRepaired yst out left right).2, by
        rw [pointAddUnequalXSubLeftSelectedEnv, if_neg h]
        rfl⟩

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
