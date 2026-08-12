import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddPostLawfulY
import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointMemory

set_option warningAsError true

/-! Lawful fixed-output readback of the G2MSM point-add postlude. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem pointAddPostStoreArgsState_fp2At (st : EvmState) (ptr : U256) :
    fp2At (pointAddPostStoreArgsState st) ptr = fp2At st ptr := by
  rfl

theorem pointAddPostFinalState_pointAt_3840 (st : EvmState)
    (left right leftY : U256)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st left))
    (hx2 : Fp2.Canonical (fp2At st right))
    (hy1 : Fp2.Canonical (fp2At st leftY))
    (hleftEnd : left.toNat + 96 < 2 ^ 256)
    (hleftAfter : 3072 ≤ left.toNat)
    (hrightEnd : right.toNat + 96 < 2 ^ 256)
    (hrightAfter : 3072 ≤ right.toNat)
    (hleftYEnd : leftY.toNat + 96 < 2 ^ 256)
    (hleftYAfter : 3072 ≤ leftY.toNat)
    (hleftPtr : pointAddPostLeft (pointAddPostState1 st) = left)
    (hrightPtr : pointAddPostRight (pointAddPostState2 st) = right)
    (hdeltaLeft : pointAddPostDeltaXLeft (pointAddPostState3 st) = left)
    (hleftYPtr : pointAddPostLeftY (pointAddPostState5 st) = leftY)
    (houtPtr : pointAddPostOut (pointAddPostState6 st) = 3840)
    (hfinite : pointZeroValue (pointAddPostFinalState st) 3840 = 0) :
    pointAt (pointAddPostFinalState st) 3840 =
      .affine
        (Fp2.toLawful (fp2At st 2048) ^ 2 -
          Fp2.toLawful (fp2At st left) - Fp2.toLawful (fp2At st right))
        (Fp2.toLawful (fp2At st 2048) *
            (Fp2.toLawful (fp2At st left) -
              (Fp2.toLawful (fp2At st 2048) ^ 2 -
                Fp2.toLawful (fp2At st left) -
                  Fp2.toLawful (fp2At st right))) -
          Fp2.toLawful (fp2At st leftY)) := by
  have hfin : pointZeroValue
      (msmStorePointState (pointAddPostStoreArgsState (pointAddPostState6 st))
        3840 2688 2944) 3840 = 0 := by
    simpa only [pointAddPostFinalState, pointAddPostStoreState, houtPtr]
      using hfinite
  have hxRead :
      fp2At (pointAddPostStoreArgsState (pointAddPostState6 st)) 2688 =
        fp2At (pointAddPostState3 st) 2688 :=
    (pointAddPostStoreArgsState_fp2At _ _).trans (pointAddPostState6_x3 st)
  have hyRead :
      fp2At (pointAddPostStoreArgsState (pointAddPostState6 st)) 2944 =
        fp2At (pointAddPostState6 st) 2944 :=
    pointAddPostStoreArgsState_fp2At _ _
  unfold pointAddPostFinalState pointAddPostStoreState
  rw [houtPtr, pointAt_storePoint_3840 _ hfin, hxRead, hyRead,
    pointAddPostState3_toLawful st left right hlam hx1 hx2
      hleftEnd hleftAfter hrightEnd hrightAfter hleftPtr hrightPtr,
    pointAddPostState6_toLawful st left right leftY hlam hx1 hx2 hy1
      hleftEnd hleftAfter hrightEnd hrightAfter hleftYEnd hleftYAfter
      hleftPtr hrightPtr hdeltaLeft hleftYPtr]

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
