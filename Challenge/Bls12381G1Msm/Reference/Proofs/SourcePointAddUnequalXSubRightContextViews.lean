import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubLeftMath

set_option warningAsError true

/-! Cached value-only projections of the concrete second-X-subtraction context. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem pointAddUnequalXSubRightContext_x3Hi (yst : EvmState)
    (out left right : U256) :
    (pointAddUnequalXSubRightContext yst out left right).x3Hi =
      (pointAddUnequalXSubLeftResult yst out left right).1 := by
  rw [pointAddUnequalXSubRightContext,
    makePointAddUnequalXSubRightContext_x3Hi]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
