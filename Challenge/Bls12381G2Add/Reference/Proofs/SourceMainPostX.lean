import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulBeforeOutLawful
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2SubPreservation
import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteDefs

set_option warningAsError true

/-! # Lawful x-coordinate postlude of frozen G2ADD -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem mainPostState0_canonical (st : EvmState)
    (hlam : Fp2.Canonical (fp2At st 2048)) :
    Fp2.Canonical (fp2At (mainPostState0 st) 2688) := by
  unfold mainPostState0
  exact fp2MulFinalState_canonical_of_high_before_out st 2688 2048 2048
    hlam hlam (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem mainPostState0_toLawful (st : EvmState)
    (hlam : Fp2.Canonical (fp2At st 2048)) :
    Fp2.toLawful (fp2At (mainPostState0 st) 2688) =
      Fp2.toLawful (fp2At st 2048) ^ 2 := by
  have h := fp2MulFinalState_toLawful_mul_of_high_before_out
    st (2688 : U256) 2048 2048 hlam hlam
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  simpa only [mainPostState0, pow_two] using h

private theorem mainPostState0_fp2At_low (st : EvmState) (ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrLow : ptr.toNat + 128 ≤ 1024) :
    fp2At (mainPostState0 st) ptr = fp2At st ptr := by
  unfold mainPostState0
  exact fp2MulFinalState_fp2At_before_scratch _ _ _ _ _
    hptrEnd hptrLow (by decide) (by decide)

private theorem mainPostState1_fp2At_low (st : EvmState) (ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrLow : ptr.toNat + 128 ≤ 1024) :
    fp2At (mainPostState1 st) ptr = fp2At st ptr := by
  unfold mainPostState1
  exact (fp2SubFinalState_fp2At_before_out _ _ _ _ _ hptrEnd
    (by bv_omega) (by decide)).trans
      (mainPostState0_fp2At_low st ptr hptrEnd hptrLow)

private theorem mainPostState1_canonical (st : EvmState)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st 0)) :
    Fp2.Canonical (fp2At (mainPostState1 st) 2688) := by
  rw [mainPostState1, fp2SubFinalState_output _ _ _ _ (by decide)]
  apply fp2SubResult_canonical
  · rw [fp2SubScheduledA_eq_at_out _ _ _ (by decide)]
    exact mainPostState0_canonical st hlam
  · rw [fp2SubScheduledB_eq_before_out _ _ _ _ (by decide) (by decide),
      mainPostState0_fp2At_low _ _ (by decide) (by decide)]
    exact hx1

private theorem mainPostState1_toLawful (st : EvmState)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st 0)) :
    Fp2.toLawful (fp2At (mainPostState1 st) 2688) =
      Fp2.toLawful (fp2At st 2048) ^ 2 - Fp2.toLawful (fp2At st 0) := by
  have hA := fp2SubScheduledA_eq_at_out
    (mainPostState0 st) (2688 : U256) 0 (by decide)
  have hB := fp2SubScheduledB_eq_before_out
    (mainPostState0 st) (2688 : U256) 2688 0 (by decide) (by decide)
  have hcanonicalA : Fp2.Canonical
      (fp2SubScheduledA (mainPostState0 st) 2688 2688 0) :=
    hA.symm ▸ mainPostState0_canonical st hlam
  have hcanonicalB : Fp2.Canonical
      (fp2SubScheduledB (mainPostState0 st) 2688 2688 0) := by
    rw [hB, mainPostState0_fp2At_low _ _ (by decide) (by decide)]
    exact hx1
  rw [mainPostState1, fp2SubFinalState_output _ _ _ _ (by decide),
    fp2SubResult_eq_subSource,
    Fp2.toLawful_subSource hcanonicalA hcanonicalB, hA, hB,
    mainPostState0_toLawful st hlam,
    mainPostState0_fp2At_low _ _ (by decide) (by decide)]

theorem mainPostState2_fp2At_low (st : EvmState) (ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrLow : ptr.toNat + 128 ≤ 1024) :
    fp2At (mainPostState2 st) ptr = fp2At st ptr := by
  unfold mainPostState2
  exact (fp2SubFinalState_fp2At_before_out _ _ _ _ _ hptrEnd
    (by bv_omega) (by decide)).trans
      (mainPostState1_fp2At_low st ptr hptrEnd hptrLow)

theorem mainPostState2_canonical (st : EvmState)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st 0))
    (hx2 : Fp2.Canonical (fp2At st 256)) :
    Fp2.Canonical (fp2At (mainPostState2 st) 2688) := by
  rw [mainPostState2, fp2SubFinalState_output _ _ _ _ (by decide)]
  apply fp2SubResult_canonical
  · rw [fp2SubScheduledA_eq_at_out _ _ _ (by decide)]
    exact mainPostState1_canonical st hlam hx1
  · rw [fp2SubScheduledB_eq_before_out _ _ _ _ (by decide) (by decide),
      mainPostState1_fp2At_low _ _ (by decide) (by decide)]
    exact hx2

theorem mainPostState2_toLawful (st : EvmState)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st 0))
    (hx2 : Fp2.Canonical (fp2At st 256)) :
    Fp2.toLawful (fp2At (mainPostState2 st) 2688) =
      Fp2.toLawful (fp2At st 2048) ^ 2 -
        Fp2.toLawful (fp2At st 0) - Fp2.toLawful (fp2At st 256) := by
  have hA := fp2SubScheduledA_eq_at_out
    (mainPostState1 st) (2688 : U256) 256 (by decide)
  have hB := fp2SubScheduledB_eq_before_out
    (mainPostState1 st) (2688 : U256) 2688 256 (by decide) (by decide)
  have hcanonicalA : Fp2.Canonical
      (fp2SubScheduledA (mainPostState1 st) 2688 2688 256) :=
    hA.symm ▸ mainPostState1_canonical st hlam hx1
  have hcanonicalB : Fp2.Canonical
      (fp2SubScheduledB (mainPostState1 st) 2688 2688 256) := by
    rw [hB, mainPostState1_fp2At_low _ _ (by decide) (by decide)]
    exact hx2
  rw [mainPostState2, fp2SubFinalState_output _ _ _ _ (by decide),
    fp2SubResult_eq_subSource,
    Fp2.toLawful_subSource hcanonicalA hcanonicalB, hA, hB,
    mainPostState1_toLawful st hlam hx1,
    mainPostState1_fp2At_low _ _ (by decide) (by decide)]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
