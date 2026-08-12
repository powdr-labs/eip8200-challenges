import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDenominatorRightLo

set_option warningAsError true

/-! Opaque memory projection after the third unequal-denominator load. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

@[simp] theorem pointAddUnequalDenominatorState6_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddUnequalDenominatorState6 yst out left right).memory =
      (pointAddUnequalNumeratorInputsState yst out left right).memory := by
  rw [pointAddUnequalDenominatorState6,
    pointAddUnequalDenominator_touchMemory_memory,
    pointAddUnequalDenominatorState5,
    pointAddUnequalDenominator_touchMemory_memory,
    pointAddUnequalDenominatorState4_memory]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
