import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddPostLawfulDelta
import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveHighPreservation

set_option warningAsError true

/-! Lawful y-coordinate half of the fixed G2MSM point-add postlude. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport
open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

private theorem nat_2944 : ((2944 : U256).toNat) = 2944 := by decide

private theorem pointAddPostState1_lambda (st : EvmState) :
    fp2At (pointAddPostState1 st) 2048 = fp2At st 2048 := by
  unfold pointAddPostState1 pointAddPostSquareState
  exact fp2MulFinalState_fp2At_before_out_high _ _ _ _ _
    (by decide) (by decide) (by decide) (by decide)

private theorem pointAddPostState2_lambda (st : EvmState) :
    fp2At (pointAddPostState2 st) 2048 = fp2At st 2048 := by
  unfold pointAddPostState2 pointAddPostSubLeftState
  exact (fp2SubFinalState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)).trans (by
      change fp2At (pointAddPostLeftReadState (pointAddPostState1 st)) 2048 =
        fp2At st 2048
      rw [pointAddPostLeftReadState_fp2At]
      exact pointAddPostState1_lambda st)

private theorem pointAddPostState3_lambda (st : EvmState) :
    fp2At (pointAddPostState3 st) 2048 = fp2At st 2048 := by
  unfold pointAddPostState3 pointAddPostSubRightState
  exact (fp2SubFinalState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)).trans (by
      change fp2At (pointAddPostRightReadState (pointAddPostState2 st)) 2048 =
        fp2At st 2048
      rw [pointAddPostRightReadState_fp2At]
      exact pointAddPostState2_lambda st)

theorem pointAddPostState4_lambda (st : EvmState) :
    fp2At (pointAddPostState4 st) 2048 = fp2At st 2048 := by
  unfold pointAddPostState4 pointAddPostDeltaXState
  exact (fp2SubFinalState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)).trans (by
      change fp2At (pointAddPostDeltaXReadState (pointAddPostState3 st)) 2048 =
        fp2At st 2048
      rw [pointAddPostDeltaXReadState_fp2At]
      exact pointAddPostState3_lambda st)

theorem pointAddPostState5_canonical (st : EvmState) (left right : U256)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st left))
    (hx2 : Fp2.Canonical (fp2At st right))
    (hleftEnd : left.toNat + 96 < 2 ^ 256)
    (hleftAfter : 3072 ≤ left.toNat)
    (hrightEnd : right.toNat + 96 < 2 ^ 256)
    (hrightAfter : 3072 ≤ right.toNat)
    (hleftPtr : pointAddPostLeft (pointAddPostState1 st) = left)
    (hrightPtr : pointAddPostRight (pointAddPostState2 st) = right)
    (hdeltaLeft : pointAddPostDeltaXLeft (pointAddPostState3 st) = left) :
    Fp2.Canonical (fp2At (pointAddPostState5 st) 2944) := by
  unfold pointAddPostState5 pointAddPostMulYState
  apply fp2MulFinalState_canonical_before
  · rw [pointAddPostState4_lambda]
    exact hlam
  · exact pointAddPostState4_canonical st left right hlam hx1 hx2
      hleftEnd hleftAfter hrightEnd hrightAfter hleftPtr hrightPtr hdeltaLeft
  all_goals decide

theorem pointAddPostState5_toLawful (st : EvmState) (left right : U256)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st left))
    (hx2 : Fp2.Canonical (fp2At st right))
    (hleftEnd : left.toNat + 96 < 2 ^ 256)
    (hleftAfter : 3072 ≤ left.toNat)
    (hrightEnd : right.toNat + 96 < 2 ^ 256)
    (hrightAfter : 3072 ≤ right.toNat)
    (hleftPtr : pointAddPostLeft (pointAddPostState1 st) = left)
    (hrightPtr : pointAddPostRight (pointAddPostState2 st) = right)
    (hdeltaLeft : pointAddPostDeltaXLeft (pointAddPostState3 st) = left) :
    Fp2.toLawful (fp2At (pointAddPostState5 st) 2944) =
      Fp2.toLawful (fp2At st 2048) *
        (Fp2.toLawful (fp2At st left) -
          (Fp2.toLawful (fp2At st 2048) ^ 2 -
            Fp2.toLawful (fp2At st left) - Fp2.toLawful (fp2At st right))) := by
  have hlam' : Fp2.Canonical (fp2At (pointAddPostState4 st) 2048) := by
    rw [pointAddPostState4_lambda]
    exact hlam
  have h := fp2MulFinalState_toLawful_before
    (pointAddPostState4 st) (2944 : U256) 2048 2816 hlam'
    (pointAddPostState4_canonical st left right hlam hx1 hx2
      hleftEnd hleftAfter hrightEnd hrightAfter hleftPtr hrightPtr hdeltaLeft)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  rw [pointAddPostState4_lambda,
    pointAddPostState4_toLawful st left right hlam hx1 hx2
      hleftEnd hleftAfter hrightEnd hrightAfter hleftPtr hrightPtr hdeltaLeft] at h
  simpa only [pointAddPostState5, pointAddPostMulYState] using h

theorem pointAddPostState5_fp2At_after (st : EvmState)
    (ptr : U256) (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrHigh : 1920 ≤ ptr.toNat)
    (hafter : 3072 ≤ ptr.toNat) :
    fp2At (pointAddPostState5 st) ptr = fp2At st ptr := by
  unfold pointAddPostState5 pointAddPostMulYState
  exact (fp2MulFinalState_fp2At_after_out _ 2944 2048 2816 ptr
    hptrEnd hptrHigh (by rw [nat_2944]; omega) (by decide)).trans
      (pointAddPostState4_fp2At_after st ptr hptrEnd hptrHigh (by omega))

theorem pointAddPostLeftYReadState_fp2At (st : EvmState)
    (ptr : U256) :
    fp2At (pointAddPostLeftYReadState st) ptr = fp2At st ptr := by
  rfl

theorem pointAddPostState6_canonical (st : EvmState)
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
    (hleftYPtr : pointAddPostLeftY (pointAddPostState5 st) = leftY) :
    Fp2.Canonical (fp2At (pointAddPostState6 st) 2944) := by
  unfold pointAddPostState6 pointAddPostSubYState
  rw [hleftYPtr]
  apply fp2SubFinalState_canonical_at_out_after
  · rw [pointAddPostLeftYReadState_fp2At]
    exact pointAddPostState5_canonical st left right hlam hx1 hx2
      hleftEnd hleftAfter hrightEnd hrightAfter hleftPtr hrightPtr hdeltaLeft
  · rw [pointAddPostLeftYReadState_fp2At,
      pointAddPostState5_fp2At_after st leftY hleftYEnd (by omega) (by omega)]
    exact hy1
  · exact hleftYEnd
  · rw [nat_2944]
    omega
  · decide

theorem pointAddPostState6_toLawful (st : EvmState)
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
    (hleftYPtr : pointAddPostLeftY (pointAddPostState5 st) = leftY) :
    Fp2.toLawful (fp2At (pointAddPostState6 st) 2944) =
      Fp2.toLawful (fp2At st 2048) *
        (Fp2.toLawful (fp2At st left) -
          (Fp2.toLawful (fp2At st 2048) ^ 2 -
            Fp2.toLawful (fp2At st left) - Fp2.toLawful (fp2At st right))) -
        Fp2.toLawful (fp2At st leftY) := by
  have hyPres := pointAddPostState5_fp2At_after st leftY hleftYEnd
    (by omega) (by omega)
  unfold pointAddPostState6 pointAddPostSubYState
  rw [hleftYPtr]
  have houtCanonical : Fp2.Canonical
      (fp2At (pointAddPostLeftYReadState (pointAddPostState5 st)) 2944) := by
    rw [pointAddPostLeftYReadState_fp2At]
    exact pointAddPostState5_canonical st left right hlam hx1 hx2
      hleftEnd hleftAfter hrightEnd hrightAfter hleftPtr hrightPtr hdeltaLeft
  have hyRead :
      fp2At (pointAddPostLeftYReadState (pointAddPostState5 st)) leftY =
        fp2At st leftY := by
    rw [pointAddPostLeftYReadState_fp2At, hyPres]
  rw [fp2SubFinalState_toLawful_at_out_after
    (pointAddPostLeftYReadState (pointAddPostState5 st)) 2944 leftY
    houtCanonical
    (by rw [pointAddPostLeftYReadState_fp2At, hyPres]; exact hy1)
    hleftYEnd (by rw [nat_2944]; omega) (by decide),
    pointAddPostLeftYReadState_fp2At,
    pointAddPostState5_toLawful st left right hlam hx1 hx2
      hleftEnd hleftAfter hrightEnd hrightAfter hleftPtr hrightPtr hdeltaLeft,
    hyRead]

private theorem pointAddPostState4_x3 (st : EvmState) :
    fp2At (pointAddPostState4 st) 2688 =
      fp2At (pointAddPostState3 st) 2688 := by
  unfold pointAddPostState4 pointAddPostDeltaXState
  exact fp2SubFinalState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide) |>.trans (by
      change fp2At (pointAddPostDeltaXReadState (pointAddPostState3 st)) 2688 =
        fp2At (pointAddPostState3 st) 2688
      rw [pointAddPostDeltaXReadState_fp2At])

private theorem pointAddPostState5_x3 (st : EvmState) :
    fp2At (pointAddPostState5 st) 2688 =
      fp2At (pointAddPostState3 st) 2688 := by
  unfold pointAddPostState5 pointAddPostMulYState
  exact (fp2MulFinalState_fp2At_before_out_high _ _ _ _ _
    (by decide) (by decide) (by decide) (by decide)).trans
      (pointAddPostState4_x3 st)

theorem pointAddPostState6_x3 (st : EvmState) :
    fp2At (pointAddPostState6 st) 2688 =
      fp2At (pointAddPostState3 st) 2688 := by
  unfold pointAddPostState6 pointAddPostSubYState
  exact (fp2SubFinalState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)).trans (by
      change fp2At (pointAddPostLeftYReadState (pointAddPostState5 st)) 2688 =
        fp2At (pointAddPostState3 st) 2688
      rw [pointAddPostLeftYReadState_fp2At]
      exact pointAddPostState5_x3 st)

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
