import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddPostLawfulX2

set_option warningAsError true

/-! Lawful `x₁ - x₃` stage of the fixed G2MSM point-add postlude. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport
open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

private theorem nat_2816 : ((2816 : U256).toNat) = 2816 := by decide

theorem pointAddPostDeltaXReadState_fp2At (st : EvmState)
    (ptr : U256) :
    fp2At (pointAddPostDeltaXReadState st) ptr = fp2At st ptr := by
  rfl

theorem pointAddPostState4_canonical (st : EvmState) (left right : U256)
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
    Fp2.Canonical (fp2At (pointAddPostState4 st) 2816) := by
  unfold pointAddPostState4 pointAddPostDeltaXState
  rw [hdeltaLeft]
  apply fp2SubFinalState_canonical_after_before
  · rw [pointAddPostDeltaXReadState_fp2At,
      pointAddPostState3_fp2At_after st left hleftEnd (by omega) (by omega)]
    exact hx1
  · rw [pointAddPostDeltaXReadState_fp2At]
    exact pointAddPostState3_canonical st left right hlam hx1 hx2
      hleftEnd hleftAfter hrightEnd hrightAfter hleftPtr hrightPtr
  · exact hleftEnd
  · rw [nat_2816]
    omega
  · decide
  · decide

theorem pointAddPostState4_toLawful (st : EvmState) (left right : U256)
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
    Fp2.toLawful (fp2At (pointAddPostState4 st) 2816) =
      Fp2.toLawful (fp2At st left) -
        (Fp2.toLawful (fp2At st 2048) ^ 2 -
          Fp2.toLawful (fp2At st left) - Fp2.toLawful (fp2At st right)) := by
  have hleftPres := pointAddPostState3_fp2At_after st left hleftEnd
    (by omega) (by omega)
  have hleftRead :
      fp2At (pointAddPostDeltaXReadState (pointAddPostState3 st)) left =
        fp2At st left :=
    (pointAddPostDeltaXReadState_fp2At _ _).trans hleftPres
  have hx3Read :
      fp2At (pointAddPostDeltaXReadState (pointAddPostState3 st)) 2688 =
        fp2At (pointAddPostState3 st) 2688 :=
    pointAddPostDeltaXReadState_fp2At _ _
  unfold pointAddPostState4 pointAddPostDeltaXState
  rw [hdeltaLeft]
  rw [fp2SubFinalState_toLawful_after_before
    (pointAddPostDeltaXReadState (pointAddPostState3 st)) 2816 left 2688
    (by rw [pointAddPostDeltaXReadState_fp2At, hleftPres]; exact hx1)
    (by rw [pointAddPostDeltaXReadState_fp2At];
        exact pointAddPostState3_canonical st left right hlam hx1 hx2
          hleftEnd hleftAfter hrightEnd hrightAfter hleftPtr hrightPtr)
    hleftEnd (by rw [nat_2816]; omega) (by decide) (by decide),
    hleftRead, hx3Read,
    pointAddPostState3_toLawful st left right hlam hx1 hx2
      hleftEnd hleftAfter hrightEnd hrightAfter hleftPtr hrightPtr]

theorem pointAddPostState4_fp2At_after (st : EvmState)
    (ptr : U256) (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrHigh : 1920 ≤ ptr.toNat)
    (hafter : 2944 ≤ ptr.toNat) :
    fp2At (pointAddPostState4 st) ptr = fp2At st ptr := by
  unfold pointAddPostState4 pointAddPostDeltaXState
  exact (fp2SubFinalState_fp2At_after_out _ 2816 _ 2688 ptr
    hptrEnd (by rw [nat_2816]; omega) (by decide)).trans (by
      rw [pointAddPostDeltaXReadState_fp2At]
      exact pointAddPostState3_fp2At_after st ptr hptrEnd hptrHigh (by omega))

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
