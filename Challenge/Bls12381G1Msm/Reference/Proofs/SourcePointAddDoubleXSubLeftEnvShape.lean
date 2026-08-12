import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubLeftSelected

set_option warningAsError true

/-! Opaque local-prefix shape of the selected first-subtraction environment. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem pointAddDoubleXSubLeftSelectedEnv_shape (yst : EvmState)
    (out left right : U256) :
    ∃ localHi localLo,
      pointAddDoubleXSubLeftSelectedEnv yst out left right =
        [("fc0_28", localHi), ("fc0_29", localLo)] ++
          pointAddDoubleX3Env yst out left right := by
  by_cases h : pointAddDoubleXSubLeftRepairValue yst out left right = 0
  · exact ⟨(pointAddDoubleXSubLeftRaw yst out left right).1,
      (pointAddDoubleXSubLeftRaw yst out left right).2, by
        rw [pointAddDoubleXSubLeftSelectedEnv, if_pos h]
        rfl⟩
  · exact ⟨(pointAddDoubleXSubLeftRepaired yst out left right).1,
      (pointAddDoubleXSubLeftRepaired yst out left right).2, by
        rw [pointAddDoubleXSubLeftSelectedEnv, if_neg h]
        rfl⟩

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
