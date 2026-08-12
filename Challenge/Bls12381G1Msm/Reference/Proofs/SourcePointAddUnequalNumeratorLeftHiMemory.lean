import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalNumeratorLeftHi

set_option warningAsError true

/-! Opaque memory projection after the second unequal-numerator load. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

@[simp] theorem pointAddUnequalNumeratorState4_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddUnequalNumeratorState4 yst out left right).memory =
      (pointAddXEqState yst out left right).memory := by
  rw [pointAddUnequalNumeratorState4, pointAddUnequal_touchMemory_memory,
    pointAddUnequalNumeratorState3, pointAddUnequal_touchMemory_memory,
    pointAddUnequalNumeratorState2_memory]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
