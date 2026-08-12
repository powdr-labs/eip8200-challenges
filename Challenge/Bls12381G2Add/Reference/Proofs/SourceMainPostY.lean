import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainPostX

set_option warningAsError true

/-! # Lawful y-coordinate postlude of frozen G2ADD -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem mainPostState3_canonical (st : EvmState)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st 0))
    (hx2 : Fp2.Canonical (fp2At st 256)) :
    Fp2.Canonical (fp2At (mainPostState3 st) 2816) := by
  rw [mainPostState3, fp2SubFinalState_output _ _ _ _ (by decide)]
  apply fp2SubResult_canonical
  · rw [fp2SubScheduledA_eq_before_out _ _ _ _ (by decide) (by decide),
      mainPostState2_fp2At_low _ _ (by decide) (by decide)]
    exact hx1
  · rw [fp2SubScheduledB_eq_before_out _ _ _ _ (by decide) (by decide)]
    exact mainPostState2_canonical st hlam hx1 hx2

theorem mainPostState3_toLawful (st : EvmState)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st 0))
    (hx2 : Fp2.Canonical (fp2At st 256)) :
    Fp2.toLawful (fp2At (mainPostState3 st) 2816) =
      Fp2.toLawful (fp2At st 0) -
        (Fp2.toLawful (fp2At st 2048) ^ 2 -
          Fp2.toLawful (fp2At st 0) - Fp2.toLawful (fp2At st 256)) := by
  have hA := fp2SubScheduledA_eq_before_out
    (mainPostState2 st) (2816 : U256) 0 2688 (by decide) (by decide)
  have hB := fp2SubScheduledB_eq_before_out
    (mainPostState2 st) (2816 : U256) 0 2688 (by decide) (by decide)
  have hcanonicalA : Fp2.Canonical
      (fp2SubScheduledA (mainPostState2 st) 2816 0 2688) := by
    rw [hA, mainPostState2_fp2At_low _ _ (by decide) (by decide)]
    exact hx1
  have hcanonicalB : Fp2.Canonical
      (fp2SubScheduledB (mainPostState2 st) 2816 0 2688) :=
    hB.symm ▸ mainPostState2_canonical st hlam hx1 hx2
  rw [mainPostState3, fp2SubFinalState_output _ _ _ _ (by decide),
    fp2SubResult_eq_subSource,
    Fp2.toLawful_subSource hcanonicalA hcanonicalB, hA, hB,
    mainPostState2_fp2At_low _ _ (by decide) (by decide),
    mainPostState2_toLawful st hlam hx1 hx2]

private theorem mainPostState0_lambda (st : EvmState) :
    fp2At (mainPostState0 st) 2048 = fp2At st 2048 := by
  unfold mainPostState0
  exact fp2MulFinalState_fp2At_before_out_high _ _ _ _ _
    (by decide) (by decide) (by decide) (by decide)

private theorem mainPostState1_lambda (st : EvmState) :
    fp2At (mainPostState1 st) 2048 = fp2At st 2048 := by
  unfold mainPostState1
  exact (fp2SubFinalState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)).trans (mainPostState0_lambda st)

private theorem mainPostState2_lambda (st : EvmState) :
    fp2At (mainPostState2 st) 2048 = fp2At st 2048 := by
  unfold mainPostState2
  exact (fp2SubFinalState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)).trans (mainPostState1_lambda st)

private theorem mainPostState3_lambda (st : EvmState) :
    fp2At (mainPostState3 st) 2048 = fp2At st 2048 := by
  unfold mainPostState3
  exact (fp2SubFinalState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)).trans (mainPostState2_lambda st)

private theorem mainPostState3_x3 (st : EvmState) :
    fp2At (mainPostState3 st) 2688 = fp2At (mainPostState2 st) 2688 := by
  unfold mainPostState3
  exact fp2SubFinalState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)

private theorem mainPostState3_fp2At_low (st : EvmState) (ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrLow : ptr.toNat + 128 ≤ 1024) :
    fp2At (mainPostState3 st) ptr = fp2At st ptr := by
  unfold mainPostState3
  exact (fp2SubFinalState_fp2At_before_out _ _ _ _ _ hptrEnd
    (by bv_omega) (by decide)).trans
      (mainPostState2_fp2At_low st ptr hptrEnd hptrLow)

theorem mainPostState4_canonical (st : EvmState)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st 0))
    (hx2 : Fp2.Canonical (fp2At st 256)) :
    Fp2.Canonical (fp2At (mainPostState4 st) 2944) := by
  unfold mainPostState4
  apply fp2MulFinalState_canonical_of_high_before_out
  · rw [mainPostState3_lambda]
    exact hlam
  · exact mainPostState3_canonical st hlam hx1 hx2
  all_goals decide

theorem mainPostState4_toLawful (st : EvmState)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st 0))
    (hx2 : Fp2.Canonical (fp2At st 256)) :
    Fp2.toLawful (fp2At (mainPostState4 st) 2944) =
      Fp2.toLawful (fp2At st 2048) *
        (Fp2.toLawful (fp2At st 0) -
          (Fp2.toLawful (fp2At st 2048) ^ 2 -
            Fp2.toLawful (fp2At st 0) - Fp2.toLawful (fp2At st 256))) := by
  have hlam' : Fp2.Canonical (fp2At (mainPostState3 st) 2048) := by
    rw [mainPostState3_lambda]
    exact hlam
  have h := fp2MulFinalState_toLawful_mul_of_high_before_out
    (mainPostState3 st) (2944 : U256) 2048 2816 hlam'
    (mainPostState3_canonical st hlam hx1 hx2)
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [mainPostState3_lambda, mainPostState3_toLawful st hlam hx1 hx2] at h
  simpa only [mainPostState4] using h

private theorem mainPostState4_x3 (st : EvmState) :
    fp2At (mainPostState4 st) 2688 = fp2At (mainPostState2 st) 2688 := by
  unfold mainPostState4
  exact (fp2MulFinalState_fp2At_before_out_high _ _ _ _ _
    (by decide) (by decide) (by decide) (by decide)).trans
      (mainPostState3_x3 st)

private theorem mainPostState4_y1 (st : EvmState) :
    fp2At (mainPostState4 st) 128 = fp2At st 128 := by
  unfold mainPostState4
  exact (fp2MulFinalState_fp2At_before_scratch _ _ _ _ _
    (by decide) (by decide) (by decide) (by decide)).trans
      (mainPostState3_fp2At_low st 128 (by decide) (by decide))

theorem mainPostState5_x3 (st : EvmState) :
    fp2At (mainPostState5 st) 2688 = fp2At (mainPostState2 st) 2688 := by
  unfold mainPostState5
  exact (fp2SubFinalState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)).trans (mainPostState4_x3 st)

theorem mainPostState5_canonical (st : EvmState)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st 0))
    (hy1 : Fp2.Canonical (fp2At st 128))
    (hx2 : Fp2.Canonical (fp2At st 256)) :
    Fp2.Canonical (fp2At (mainPostState5 st) 2944) := by
  rw [mainPostState5, fp2SubFinalState_output _ _ _ _ (by decide)]
  apply fp2SubResult_canonical
  · rw [fp2SubScheduledA_eq_at_out _ _ _ (by decide)]
    exact mainPostState4_canonical st hlam hx1 hx2
  · rw [fp2SubScheduledB_eq_before_out _ _ _ _ (by decide) (by decide),
      mainPostState4_y1]
    exact hy1

theorem mainPostState5_toLawful (st : EvmState)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st 0))
    (hy1 : Fp2.Canonical (fp2At st 128))
    (hx2 : Fp2.Canonical (fp2At st 256)) :
    Fp2.toLawful (fp2At (mainPostState5 st) 2944) =
      Fp2.toLawful (fp2At st 2048) *
        (Fp2.toLawful (fp2At st 0) -
          (Fp2.toLawful (fp2At st 2048) ^ 2 -
            Fp2.toLawful (fp2At st 0) - Fp2.toLawful (fp2At st 256))) -
        Fp2.toLawful (fp2At st 128) := by
  have hA := fp2SubScheduledA_eq_at_out
    (mainPostState4 st) (2944 : U256) 128 (by decide)
  have hB := fp2SubScheduledB_eq_before_out
    (mainPostState4 st) (2944 : U256) 2944 128 (by decide) (by decide)
  have hcanonicalA : Fp2.Canonical
      (fp2SubScheduledA (mainPostState4 st) 2944 2944 128) :=
    hA.symm ▸ mainPostState4_canonical st hlam hx1 hx2
  have hcanonicalB : Fp2.Canonical
      (fp2SubScheduledB (mainPostState4 st) 2944 2944 128) := by
    rw [hB, mainPostState4_y1]
    exact hy1
  rw [mainPostState5, fp2SubFinalState_output _ _ _ _ (by decide),
    fp2SubResult_eq_subSource,
    Fp2.toLawful_subSource hcanonicalA hcanonicalB, hA, hB,
    mainPostState4_toLawful st hlam hx1 hx2, mainPostState4_y1]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
