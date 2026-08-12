import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalInvPrefix

set_option warningAsError true

/-! State bridge from the inlined unequal inversion to the shared `fpInv` input. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem pointAddUnequalInvInputStateGeneric_eq_fpInvInputState
    (yst : EvmState) (hi lo : U256) :
    pointAddUnequalInvInputStateGeneric yst hi lo =
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvInputState
        yst hi lo := by
  rfl

theorem pointAddUnequalInvInputState_eq_fpInvInputState
    (yst : EvmState) (out left right : U256) :
    pointAddUnequalInvInputState yst out left right =
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvInputState
        (pointAddUnequalNumeratorInputsState yst out left right)
        (pointAddUnequalDenominatorResult yst out left right).1
        (pointAddUnequalDenominatorResult yst out left right).2 := by
  exact pointAddUnequalInvInputStateGeneric_eq_fpInvInputState _ _ _

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
