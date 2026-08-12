import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalReadbackXValue
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalReadbackY

set_option warningAsError true

/-! Transport unequal affine-addition readback to the concrete output pointer. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem pointAddUnequalPostOut_fits (yst : EvmState)
    (out left right : U256) (hout : out.toNat + 96 < 2 ^ 256) :
    (pointAddUnequalPostOut
      (pointAddUnequalPostContext yst out left right)).toNat + 96 <
      2 ^ 256 := by
  rw [pointAddUnequalPostOut_eq]
  exact hout

theorem pointAddUnequalFinalState_readbackX (yst : EvmState)
    (out left right : U256) (hout : out.toNat + 96 < 2 ^ 256) :
    pointMemoryX (pointAddUnequalFinalState yst out left right) out =
      pointAddUnequalOutputX yst out left right := by
  let ctx := pointAddUnequalPostContext yst out left right
  let st := pointAddUnequalPostState ctx
  let postOut := pointAddUnequalPostOut ctx
  have hp : postOut = out := pointAddUnequalPostOut_eq yst out left right
  calc
    pointMemoryX st out = pointMemoryX st postOut :=
      congrArg (pointMemoryX st) hp.symm
    _ = pointAddUnequalOutputX yst out left right :=
      pointAddUnequalConcretePostState_readbackXValue yst out left right
        (pointAddUnequalPostOut_fits yst out left right hout)

theorem pointAddUnequalFinalState_readbackY (yst : EvmState)
    (out left right : U256) (hout : out.toNat + 96 < 2 ^ 256) :
    pointMemoryY (pointAddUnequalFinalState yst out left right) out =
      pointAddUnequalOutputY yst out left right := by
  let ctx := pointAddUnequalPostContext yst out left right
  let st := pointAddUnequalPostState ctx
  let postOut := pointAddUnequalPostOut ctx
  have hp : postOut = out := pointAddUnequalPostOut_eq yst out left right
  calc
    pointMemoryY st out = pointMemoryY st postOut :=
      congrArg (pointMemoryY st) hp.symm
    _ = pointAddUnequalOutputY yst out left right :=
      pointAddUnequalConcretePostState_readbackYValue yst out left right
        (pointAddUnequalPostOut_fits yst out left right hout)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
