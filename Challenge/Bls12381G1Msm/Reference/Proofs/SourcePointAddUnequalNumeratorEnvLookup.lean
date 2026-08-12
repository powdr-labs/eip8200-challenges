import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalNumeratorFull

set_option warningAsError true

/-! Opaque numerator-result projections for later unequal-point operations. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem pointAddUnequalNumeratorEnv_hi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalNumeratorEnv yst out left right) "\x00128" =
      some (pointAddUnequalNumeratorResult yst out left right).1 := by
  rfl

theorem pointAddUnequalNumeratorEnv_lo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalNumeratorEnv yst out left right) "\x00129" =
      some (pointAddUnequalNumeratorResult yst out left right).2 := by
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
