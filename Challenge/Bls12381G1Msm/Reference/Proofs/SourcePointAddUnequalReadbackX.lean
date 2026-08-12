import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalReadback

set_option warningAsError true

/-! X readback specialized to the concrete post-context, without unfolding it. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem pointAddUnequalConcretePostState_readbackX (yst : EvmState)
    (out left right : U256)
    (hptr :
      (pointAddUnequalPostOut
        (pointAddUnequalPostContext yst out left right)).toNat + 96 <
        2 ^ 256) :
    pointMemoryX
        (pointAddUnequalPostState
          (pointAddUnequalPostContext yst out left right))
        (pointAddUnequalPostOut
          (pointAddUnequalPostContext yst out left right)) =
      ({ hi := YulEvmCompiler.conv
          (pointAddUnequalPostContext yst out left right).xHi
         lo := YulEvmCompiler.conv
          (pointAddUnequalPostContext yst out left right).xLo } : Fp.Limbs) :=
  (pointAddUnequalPostState_readback
    (pointAddUnequalPostContext yst out left right) hptr).1

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
