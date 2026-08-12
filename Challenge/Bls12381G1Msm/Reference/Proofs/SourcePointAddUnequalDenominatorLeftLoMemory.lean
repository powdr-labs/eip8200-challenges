import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDenominatorLeftLo

set_option warningAsError true

/-! Opaque memory projection after the first unequal-denominator load. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

@[simp] theorem pointAddUnequalDenominatorState2_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddUnequalDenominatorState2 yst out left right).memory =
      (pointAddUnequalNumeratorInputsState yst out left right).memory := by
  rw [pointAddUnequalDenominatorState2,
    pointAddUnequalDenominator_touchMemory_memory,
    pointAddUnequalDenominatorState1,
    pointAddUnequalDenominator_touchMemory_memory]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
