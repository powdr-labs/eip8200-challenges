import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalNumeratorRightHi

set_option warningAsError true

/-! Opaque memory projection after all unequal-numerator input loads. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

@[simp] theorem pointAddUnequalNumeratorInputsState_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddUnequalNumeratorInputsState yst out left right).memory =
      (pointAddXEqState yst out left right).memory := by
  rw [pointAddUnequalNumeratorInputsState, pointAddUnequal_touchMemory_memory,
    pointAddUnequalNumeratorState7, pointAddUnequal_touchMemory_memory,
    pointAddUnequalNumeratorState6_memory]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
