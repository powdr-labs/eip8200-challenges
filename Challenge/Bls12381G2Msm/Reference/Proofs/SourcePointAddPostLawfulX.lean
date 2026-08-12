import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2AfterOutPreservation
import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddPost

set_option warningAsError true

/-! Lawful x-coordinate half of the fixed G2MSM affine postlude. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport
open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

private theorem nat_2688 : ((2688 : U256).toNat) = 2688 := by decide

theorem pointAddPostState1_canonical (st : EvmState)
    (hlam : Fp2.Canonical (fp2At st 2048)) :
    Fp2.Canonical (fp2At (pointAddPostState1 st) 2688) := by
  unfold pointAddPostState1 pointAddPostSquareState
  exact fp2MulFinalState_canonical_before st 2688 2048 2048 hlam hlam
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem pointAddPostState1_toLawful (st : EvmState)
    (hlam : Fp2.Canonical (fp2At st 2048)) :
    Fp2.toLawful (fp2At (pointAddPostState1 st) 2688) =
      Fp2.toLawful (fp2At st 2048) ^ 2 := by
  have h := fp2MulFinalState_toLawful_before st 2688 2048 2048 hlam hlam
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  simpa only [pointAddPostState1, pointAddPostSquareState, pow_two] using h

theorem pointAddPostState1_fp2At_after (st : EvmState)
    (ptr : U256) (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrHigh : 1920 ≤ ptr.toNat)
    (hafter : 2816 ≤ ptr.toNat) :
    fp2At (pointAddPostState1 st) ptr = fp2At st ptr := by
  unfold pointAddPostState1 pointAddPostSquareState
  exact fp2MulFinalState_fp2At_after_out st 2688 2048 2048 ptr
    hptrEnd hptrHigh (by rw [nat_2688]; omega) (by decide)

theorem pointAddPostLeftReadState_fp2At (st : EvmState)
    (ptr : U256) :
    fp2At (pointAddPostLeftReadState st) ptr = fp2At st ptr := by
  rfl

theorem pointAddPostState2_canonical (st : EvmState) (left : U256)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st left))
    (hleftEnd : left.toNat + 96 < 2 ^ 256)
    (hleftAfter : 3072 ≤ left.toNat)
    (hleftPtr : pointAddPostLeft (pointAddPostState1 st) = left) :
    Fp2.Canonical (fp2At (pointAddPostState2 st) 2688) := by
  unfold pointAddPostState2 pointAddPostSubLeftState
  rw [hleftPtr]
  apply fp2SubFinalState_canonical_at_out_after
  · rw [pointAddPostLeftReadState_fp2At]
    exact pointAddPostState1_canonical st hlam
  · rw [pointAddPostLeftReadState_fp2At,
      pointAddPostState1_fp2At_after st left hleftEnd (by omega)
      (by omega)]
    exact hx1
  · exact hleftEnd
  · rw [nat_2688]
    omega
  · decide

theorem pointAddPostState2_toLawful (st : EvmState) (left : U256)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st left))
    (hleftEnd : left.toNat + 96 < 2 ^ 256)
    (hleftAfter : 3072 ≤ left.toNat)
    (hleftPtr : pointAddPostLeft (pointAddPostState1 st) = left) :
    Fp2.toLawful (fp2At (pointAddPostState2 st) 2688) =
      Fp2.toLawful (fp2At st 2048) ^ 2 -
        Fp2.toLawful (fp2At st left) := by
  have hleftPres := pointAddPostState1_fp2At_after st left hleftEnd
    (by omega) (by omega)
  unfold pointAddPostState2 pointAddPostSubLeftState
  rw [hleftPtr]
  have houtCanonical : Fp2.Canonical
      (fp2At (pointAddPostLeftReadState (pointAddPostState1 st)) 2688) := by
    rw [pointAddPostLeftReadState_fp2At]
    exact pointAddPostState1_canonical st hlam
  have hleftRead :
      fp2At (pointAddPostLeftReadState (pointAddPostState1 st)) left =
        fp2At st left := by
    rw [pointAddPostLeftReadState_fp2At, hleftPres]
  rw [fp2SubFinalState_toLawful_at_out_after
    (pointAddPostLeftReadState (pointAddPostState1 st)) 2688 left
    houtCanonical
    (by rw [pointAddPostLeftReadState_fp2At, hleftPres]; exact hx1)
    hleftEnd (by rw [nat_2688]; omega) (by decide),
    pointAddPostLeftReadState_fp2At,
    pointAddPostState1_toLawful st hlam, hleftRead]

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
