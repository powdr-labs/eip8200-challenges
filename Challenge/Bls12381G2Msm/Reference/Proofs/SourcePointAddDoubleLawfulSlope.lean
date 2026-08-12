import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddDoubleLawful
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvCorrect

set_option warningAsError true

/-! Lawful denominator, inverse, and slope for fixed-layout G2MSM doubling. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private theorem nat_2432 : ((2432 : U256).toNat) = 2432 := by decide

private theorem pointAddDoubleDenRead2_fp2At (st : EvmState)
    (ptr : U256) :
    fp2At (pointAddDoubleDenRead2 st) ptr = fp2At st ptr := by
  rfl

theorem pointAddDoubleDenState_canonical (st : EvmState) (y : U256)
    (hy : Fp2.Canonical (fp2At st y))
    (hyEnd : y.toNat + 96 < 2 ^ 256)
    (hyHigh : 3072 ≤ y.toNat)
    (hy1 : pointAddDoubleDenY1 st = y)
    (hy2 : pointAddDoubleDenY2 st = y) :
    Fp2.Canonical (fp2At (pointAddDoubleDenState st) 2432) := by
  unfold pointAddDoubleDenState
  rw [hy1, hy2]
  apply fp2AddFinalState_canonical_after
  · rw [pointAddDoubleDenRead2_fp2At]
    exact hy
  · rw [pointAddDoubleDenRead2_fp2At]
    exact hy
  · exact hyEnd
  · rw [nat_2432]
    omega
  · exact hyEnd
  · rw [nat_2432]
    omega
  · decide

theorem pointAddDoubleDenState_toLawful (st : EvmState) (y : U256)
    (hy : Fp2.Canonical (fp2At st y))
    (hyEnd : y.toNat + 96 < 2 ^ 256)
    (hyHigh : 3072 ≤ y.toNat)
    (hy1 : pointAddDoubleDenY1 st = y)
    (hy2 : pointAddDoubleDenY2 st = y) :
    Fp2.toLawful (fp2At (pointAddDoubleDenState st) 2432) =
      2 * Fp2.toLawful (fp2At st y) := by
  unfold pointAddDoubleDenState
  rw [hy1, hy2]
  have h := fp2AddFinalState_toLawful_after
    (pointAddDoubleDenRead2 st) 2432 y y
    (by rw [pointAddDoubleDenRead2_fp2At]; exact hy)
    (by rw [pointAddDoubleDenRead2_fp2At]; exact hy)
    hyEnd (by rw [nat_2432]; omega)
    hyEnd (by rw [nat_2432]; omega) (by decide)
  rw [pointAddDoubleDenRead2_fp2At] at h
  calc
    Fp2.toLawful (fp2At
        (fp2AddFinalState (pointAddDoubleDenRead2 st) 2432 y y) 2432) =
        Fp2.toLawful (fp2At st y) + Fp2.toLawful (fp2At st y) := h
    _ = 2 * Fp2.toLawful (fp2At st y) := by ring

theorem pointAddDoubleInvState_canonical (st : EvmState)
    (hden : Fp2.Canonical (fp2At st 2432)) :
    Fp2.Canonical (fp2At (pointAddDoubleInvState st) 2560) := by
  unfold pointAddDoubleInvState
  change Fp2.Canonical
    (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvFinalState
        st 2560 2432) 2560)
  rw [Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvFinalState_eq_recovered
    _ _ _ hden
      (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.canonical_fp2InvRecovered hden

theorem pointAddDoubleInvState_toLawful (st : EvmState)
    (hden : Fp2.Canonical (fp2At st 2432)) :
    Fp2.toLawful (fp2At (pointAddDoubleInvState st) 2560) =
      (Fp2.toLawful (fp2At st 2432))⁻¹ := by
  unfold pointAddDoubleInvState
  exact Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvFinalState_toLawful
    st 2560 2432 hden
      (by decide) (by decide) (by decide) (by decide) (by decide)

theorem pointAddDoubleSlopeState_canonical (st : EvmState)
    (hnum : Fp2.Canonical (fp2At st 2304))
    (hinv : Fp2.Canonical (fp2At st 2560)) :
    Fp2.Canonical (fp2At (pointAddDoubleSlopeState st) 2048) := by
  unfold pointAddDoubleSlopeState
  exact fp2MulFinalState_canonical_after st 2048 2304 2560 hnum hinv
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem pointAddDoubleSlopeState_toLawful (st : EvmState)
    (hnum : Fp2.Canonical (fp2At st 2304))
    (hinv : Fp2.Canonical (fp2At st 2560)) :
    Fp2.toLawful (fp2At (pointAddDoubleSlopeState st) 2048) =
      Fp2.toLawful (fp2At st 2304) *
        Fp2.toLawful (fp2At st 2560) := by
  unfold pointAddDoubleSlopeState
  exact fp2MulFinalState_toLawful_after st 2048 2304 2560 hnum hinv
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
