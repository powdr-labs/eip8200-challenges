import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddPostLawfulX

set_option warningAsError true

/-! Lawful completion of the fixed G2MSM point-add x-coordinate. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport
open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

private theorem nat_2688 : ((2688 : U256).toNat) = 2688 := by decide

theorem pointAddPostState2_fp2At_after (st : EvmState)
    (ptr : U256) (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrHigh : 1920 ≤ ptr.toNat)
    (hafter : 2816 ≤ ptr.toNat) :
    fp2At (pointAddPostState2 st) ptr = fp2At st ptr := by
  unfold pointAddPostState2 pointAddPostSubLeftState
  exact (fp2SubFinalState_fp2At_after_out _ 2688 2688 _ ptr
    hptrEnd (by rw [nat_2688]; omega) (by decide)).trans (by
      rw [pointAddPostLeftReadState_fp2At]
      exact pointAddPostState1_fp2At_after st ptr hptrEnd hptrHigh hafter)

theorem pointAddPostRightReadState_fp2At (st : EvmState)
    (ptr : U256) :
    fp2At (pointAddPostRightReadState st) ptr = fp2At st ptr := by
  rfl

theorem pointAddPostState3_canonical (st : EvmState) (left right : U256)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st left))
    (hx2 : Fp2.Canonical (fp2At st right))
    (hleftEnd : left.toNat + 96 < 2 ^ 256)
    (hleftAfter : 3072 ≤ left.toNat)
    (hrightEnd : right.toNat + 96 < 2 ^ 256)
    (hrightAfter : 3072 ≤ right.toNat)
    (hleftPtr : pointAddPostLeft (pointAddPostState1 st) = left)
    (hrightPtr : pointAddPostRight (pointAddPostState2 st) = right) :
    Fp2.Canonical (fp2At (pointAddPostState3 st) 2688) := by
  unfold pointAddPostState3 pointAddPostSubRightState
  rw [hrightPtr]
  apply fp2SubFinalState_canonical_at_out_after
  · rw [pointAddPostRightReadState_fp2At]
    exact pointAddPostState2_canonical st left hlam hx1 hleftEnd hleftAfter hleftPtr
  · rw [pointAddPostRightReadState_fp2At,
      pointAddPostState2_fp2At_after st right hrightEnd (by omega) (by omega)]
    exact hx2
  · exact hrightEnd
  · rw [nat_2688]
    omega
  · decide

theorem pointAddPostState3_toLawful (st : EvmState) (left right : U256)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st left))
    (hx2 : Fp2.Canonical (fp2At st right))
    (hleftEnd : left.toNat + 96 < 2 ^ 256)
    (hleftAfter : 3072 ≤ left.toNat)
    (hrightEnd : right.toNat + 96 < 2 ^ 256)
    (hrightAfter : 3072 ≤ right.toNat)
    (hleftPtr : pointAddPostLeft (pointAddPostState1 st) = left)
    (hrightPtr : pointAddPostRight (pointAddPostState2 st) = right) :
    Fp2.toLawful (fp2At (pointAddPostState3 st) 2688) =
      Fp2.toLawful (fp2At st 2048) ^ 2 -
        Fp2.toLawful (fp2At st left) - Fp2.toLawful (fp2At st right) := by
  have hrightPres := pointAddPostState2_fp2At_after st right hrightEnd
    (by omega) (by omega)
  unfold pointAddPostState3 pointAddPostSubRightState
  rw [hrightPtr]
  have houtCanonical : Fp2.Canonical
      (fp2At (pointAddPostRightReadState (pointAddPostState2 st)) 2688) := by
    rw [pointAddPostRightReadState_fp2At]
    exact pointAddPostState2_canonical st left hlam hx1 hleftEnd hleftAfter hleftPtr
  have hrightRead :
      fp2At (pointAddPostRightReadState (pointAddPostState2 st)) right =
        fp2At st right := by
    rw [pointAddPostRightReadState_fp2At, hrightPres]
  rw [fp2SubFinalState_toLawful_at_out_after
    (pointAddPostRightReadState (pointAddPostState2 st)) 2688 right
    houtCanonical
    (by rw [pointAddPostRightReadState_fp2At, hrightPres]; exact hx2)
    hrightEnd (by rw [nat_2688]; omega) (by decide),
    pointAddPostRightReadState_fp2At,
    pointAddPostState2_toLawful st left hlam hx1 hleftEnd hleftAfter hleftPtr,
    hrightRead]

theorem pointAddPostState3_fp2At_after (st : EvmState)
    (ptr : U256) (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrHigh : 1920 ≤ ptr.toNat)
    (hafter : 2816 ≤ ptr.toNat) :
    fp2At (pointAddPostState3 st) ptr = fp2At st ptr := by
  unfold pointAddPostState3 pointAddPostSubRightState
  exact (fp2SubFinalState_fp2At_after_out _ 2688 2688 _ ptr
    hptrEnd (by rw [nat_2688]; omega) (by decide)).trans (by
      rw [pointAddPostRightReadState_fp2At]
      exact pointAddPostState2_fp2At_after st ptr hptrEnd hptrHigh hafter)

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
