import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDenominatorLeftHi

set_option warningAsError true

/-! Opaque memory projection after the second unequal-denominator load. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

@[simp] theorem pointAddUnequalDenominatorState4_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddUnequalDenominatorState4 yst out left right).memory =
      (pointAddUnequalNumeratorInputsState yst out left right).memory := by
  rw [pointAddUnequalDenominatorState4,
    pointAddUnequalDenominator_touchMemory_memory,
    pointAddUnequalDenominatorState3,
    pointAddUnequalDenominator_touchMemory_memory,
    pointAddUnequalDenominatorState2_memory]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
