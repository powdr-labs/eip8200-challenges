import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalNumeratorLeftLo

set_option warningAsError true

/-! Opaque memory projection after the first unequal-numerator load. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

@[simp] theorem pointAddUnequalNumeratorState2_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddUnequalNumeratorState2 yst out left right).memory =
      (pointAddXEqState yst out left right).memory := by
  rw [pointAddUnequalNumeratorState2, pointAddUnequal_touchMemory_memory,
    pointAddUnequalNumeratorState1, pointAddUnequal_touchMemory_memory]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
