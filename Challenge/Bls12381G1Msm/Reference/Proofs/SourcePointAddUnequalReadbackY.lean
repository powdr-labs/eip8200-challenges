import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalReadback

set_option warningAsError true

/-! Assemble the concrete unequal Y output through its opaque word pair. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

def pointAddUnequalOutputY (yst : EvmState) (out left right : U256) :
    Fp.Limbs :=
  { hi := YulEvmCompiler.conv
      (pointAddUnequalPostY yst out left right).1
    lo := YulEvmCompiler.conv
      (pointAddUnequalPostY yst out left right).2 }

theorem pointAddUnequalConcretePostState_readbackYValue (yst : EvmState)
    (out left right : U256)
    (hptr :
      (pointAddUnequalPostOut
        (pointAddUnequalPostContext yst out left right)).toNat + 96 <
        2 ^ 256) :
    pointMemoryY
        (pointAddUnequalPostState
          (pointAddUnequalPostContext yst out left right))
        (pointAddUnequalPostOut
          (pointAddUnequalPostContext yst out left right)) =
      pointAddUnequalOutputY yst out left right := by
  calc
    _ = ({
      hi := YulEvmCompiler.conv
        (pointAddUnequalPostContext yst out left right).yHi
      lo := YulEvmCompiler.conv
        (pointAddUnequalPostContext yst out left right).yLo } : Fp.Limbs) :=
      (pointAddUnequalPostState_readback
        (pointAddUnequalPostContext yst out left right) hptr).2
    _ = pointAddUnequalOutputY yst out left right := by
      rw [pointAddUnequalPostContext_yHi,
        pointAddUnequalPostContext_yLo]
      rfl

theorem pointAddUnequalOutputY_eq_result (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalOutputY yst out left right =
      ({ hi := YulEvmCompiler.conv
          (pointAddUnequalYSubResult
            (pointAddUnequalYSubContext yst out left right)).1
         lo := YulEvmCompiler.conv
          (pointAddUnequalYSubResult
            (pointAddUnequalYSubContext yst out left right)).2 } : Fp.Limbs) := by
  rw [pointAddUnequalOutputY, pointAddUnequalPostY_eq]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
