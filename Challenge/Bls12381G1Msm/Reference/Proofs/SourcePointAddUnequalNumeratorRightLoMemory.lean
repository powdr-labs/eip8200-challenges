import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalNumeratorRightLo

set_option warningAsError true

/-! Opaque memory projection after the third unequal-numerator load. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

@[simp] theorem pointAddUnequalNumeratorState6_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddUnequalNumeratorState6 yst out left right).memory =
      (pointAddXEqState yst out left right).memory := by
  rw [pointAddUnequalNumeratorState6, pointAddUnequal_touchMemory_memory,
    pointAddUnequalNumeratorState5, pointAddUnequal_touchMemory_memory,
    pointAddUnequalNumeratorState4_memory]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
