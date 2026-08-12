import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDenominatorFull

set_option warningAsError true

/-! Small concrete environment projection after unequal-denominator output. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem pointAddUnequalDenominatorEnv_eq (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalDenominatorEnv yst out left right =
      [("\x00130", (pointAddUnequalDenominatorResult yst out left right).1),
       ("\x00131", (pointAddUnequalDenominatorResult yst out left right).2)] ++
        pointAddUnequalNumeratorEnv yst out left right := by
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
