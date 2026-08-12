import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteInputs
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2SubPreservation

set_option warningAsError true

/-! # Lawful coordinate differences of frozen G2ADD unequal addition -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem mainUnequalState0_canonical (yst : EvmState)
    (hy1 : Fp2.Canonical (fp2At (mainValidatedState yst) 128))
    (hy2 : Fp2.Canonical (fp2At (mainValidatedState yst) 384)) :
    Fp2.Canonical (fp2At (mainUnequalState0 yst) 2304) := by
  rw [mainUnequalState0, fp2SubFinalState_output _ _ _ _ (by decide)]
  apply fp2SubResult_canonical
  · rw [fp2SubScheduledA_eq_before_out _ _ _ _ (by decide) (by decide),
      mainAfterFiniteXEq2_fp2At]
    exact hy2
  · rw [fp2SubScheduledB_eq_before_out _ _ _ _ (by decide) (by decide),
      mainAfterFiniteXEq2_fp2At]
    exact hy1

theorem mainUnequalState0_toLawful (yst : EvmState)
    (hy1 : Fp2.Canonical (fp2At (mainValidatedState yst) 128))
    (hy2 : Fp2.Canonical (fp2At (mainValidatedState yst) 384)) :
    Fp2.toLawful (fp2At (mainUnequalState0 yst) 2304) =
      Fp2.toLawful (fp2At (mainValidatedState yst) 384) -
        Fp2.toLawful (fp2At (mainValidatedState yst) 128) := by
  have hA := fp2SubScheduledA_eq_before_out
    (mainAfterFiniteXEq2 yst) (2304 : U256) 384 128 (by decide) (by decide)
  have hB := fp2SubScheduledB_eq_before_out
    (mainAfterFiniteXEq2 yst) (2304 : U256) 384 128 (by decide) (by decide)
  have hcanonicalA : Fp2.Canonical
      (fp2SubScheduledA (mainAfterFiniteXEq2 yst) 2304 384 128) := by
    rw [hA, mainAfterFiniteXEq2_fp2At]
    exact hy2
  have hcanonicalB : Fp2.Canonical
      (fp2SubScheduledB (mainAfterFiniteXEq2 yst) 2304 384 128) := by
    rw [hB, mainAfterFiniteXEq2_fp2At]
    exact hy1
  rw [mainUnequalState0, fp2SubFinalState_output _ _ _ _ (by decide),
    fp2SubResult_eq_subSource,
    Fp2.toLawful_subSource hcanonicalA hcanonicalB, hA, hB,
    mainAfterFiniteXEq2_fp2At yst 384,
    mainAfterFiniteXEq2_fp2At yst 128]

theorem mainUnequalState0_fp2At_low (yst : EvmState) (ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hbefore : ptr.toNat + 128 ≤ (2304 : U256).toNat) :
    fp2At (mainUnequalState0 yst) ptr = fp2At (mainValidatedState yst) ptr := by
  unfold mainUnequalState0
  exact (fp2SubFinalState_fp2At_before_out _ (2304 : U256) 384 128 ptr
    hptrEnd hbefore
    (by decide)).trans (mainAfterFiniteXEq2_fp2At yst ptr)

theorem mainUnequalState1_canonical (yst : EvmState)
    (hx1 : Fp2.Canonical (fp2At (mainValidatedState yst) 0))
    (hx2 : Fp2.Canonical (fp2At (mainValidatedState yst) 256)) :
    Fp2.Canonical (fp2At (mainUnequalState1 yst) 2432) := by
  rw [mainUnequalState1, fp2SubFinalState_output _ _ _ _ (by decide)]
  apply fp2SubResult_canonical
  · rw [fp2SubScheduledA_eq_before_out _ _ _ _ (by decide) (by decide),
      mainUnequalState0_fp2At_low yst 256 (by decide) (by decide)]
    exact hx2
  · rw [fp2SubScheduledB_eq_before_out _ _ _ _ (by decide) (by decide),
      mainUnequalState0_fp2At_low yst 0 (by decide) (by decide)]
    exact hx1

theorem mainUnequalState1_toLawful (yst : EvmState)
    (hx1 : Fp2.Canonical (fp2At (mainValidatedState yst) 0))
    (hx2 : Fp2.Canonical (fp2At (mainValidatedState yst) 256)) :
    Fp2.toLawful (fp2At (mainUnequalState1 yst) 2432) =
      Fp2.toLawful (fp2At (mainValidatedState yst) 256) -
        Fp2.toLawful (fp2At (mainValidatedState yst) 0) := by
  have hA := fp2SubScheduledA_eq_before_out
    (mainUnequalState0 yst) (2432 : U256) 256 0 (by decide) (by decide)
  have hB := fp2SubScheduledB_eq_before_out
    (mainUnequalState0 yst) (2432 : U256) 256 0 (by decide) (by decide)
  have hcanonicalA : Fp2.Canonical
      (fp2SubScheduledA (mainUnequalState0 yst) 2432 256 0) := by
    rw [hA, mainUnequalState0_fp2At_low yst 256 (by decide) (by decide)]
    exact hx2
  have hcanonicalB : Fp2.Canonical
      (fp2SubScheduledB (mainUnequalState0 yst) 2432 256 0) := by
    rw [hB, mainUnequalState0_fp2At_low yst 0 (by decide) (by decide)]
    exact hx1
  rw [mainUnequalState1, fp2SubFinalState_output _ _ _ _ (by decide),
    fp2SubResult_eq_subSource,
    Fp2.toLawful_subSource hcanonicalA hcanonicalB, hA, hB,
    mainUnequalState0_fp2At_low yst 256 (by decide) (by decide),
    mainUnequalState0_fp2At_low yst 0 (by decide) (by decide)]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
