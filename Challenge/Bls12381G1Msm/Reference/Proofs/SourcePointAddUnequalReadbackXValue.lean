import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalReadbackX

set_option warningAsError true

/-! Assemble the concrete unequal X output through its opaque word pair. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

def pointAddUnequalOutputX (yst : EvmState) (out left right : U256) :
    Fp.Limbs :=
  { hi := YulEvmCompiler.conv
      (pointAddUnequalPostX yst out left right).1
    lo := YulEvmCompiler.conv
      (pointAddUnequalPostX yst out left right).2 }

theorem pointAddUnequalConcretePostState_readbackXValue (yst : EvmState)
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
      pointAddUnequalOutputX yst out left right := by
  calc
    _ = ({
      hi := YulEvmCompiler.conv
        (pointAddUnequalPostContext yst out left right).xHi
      lo := YulEvmCompiler.conv
        (pointAddUnequalPostContext yst out left right).xLo } : Fp.Limbs) :=
      pointAddUnequalConcretePostState_readbackX yst out left right hptr
    _ = pointAddUnequalOutputX yst out left right := by
      rw [pointAddUnequalPostContext_xHi,
        pointAddUnequalPostContext_xLo]
      rfl

theorem pointAddUnequalOutputX_eq_result (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalOutputX yst out left right =
      ({ hi := YulEvmCompiler.conv
          (pointAddUnequalXSubResult yst out left right).1
         lo := YulEvmCompiler.conv
          (pointAddUnequalXSubResult yst out left right).2 } : Fp.Limbs) := by
  rw [pointAddUnequalOutputX, pointAddUnequalPostX_eq]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
