import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainUnequalDifferences
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvCorrect
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvPreservation

set_option warningAsError true

/-! # Lawful inverse phase of frozen G2ADD unequal addition -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem mainUnequalState2_canonical (yst : EvmState)
    (hx1 : Fp2.Canonical (fp2At (mainValidatedState yst) 0))
    (hx2 : Fp2.Canonical (fp2At (mainValidatedState yst) 256)) :
    Fp2.Canonical (fp2At (mainUnequalState2 yst) 2560) := by
  have hden := mainUnequalState1_canonical yst hx1 hx2
  unfold mainUnequalState2
  rw [fp2InvFinalState_eq_recovered _ _ _ hden
    (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact canonical_fp2InvRecovered hden

theorem mainUnequalState2_toLawful (yst : EvmState)
    (hx1 : Fp2.Canonical (fp2At (mainValidatedState yst) 0))
    (hx2 : Fp2.Canonical (fp2At (mainValidatedState yst) 256)) :
    Fp2.toLawful (fp2At (mainUnequalState2 yst) 2560) =
      (Fp2.toLawful (fp2At (mainValidatedState yst) 256) -
        Fp2.toLawful (fp2At (mainValidatedState yst) 0))⁻¹ := by
  have h := fp2InvFinalState_toLawful
    (mainUnequalState1 yst) (2560 : U256) 2432
    (mainUnequalState1_canonical yst hx1 hx2)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [mainUnequalState1_toLawful yst hx1 hx2] at h
  simpa only [mainUnequalState2] using h

theorem mainUnequalInvNorm_hi_lt (yst : EvmState)
    (hx1 : Fp2.Canonical (fp2At (mainValidatedState yst) 0))
    (hx2 : Fp2.Canonical (fp2At (mainValidatedState yst) 256)) :
    (fp2InvNorm (mainUnequalState1 yst) 2432).1.toNat < 2 ^ 128 := by
  exact fp2InvNorm_hi_lt_of_input (mainUnequalState1 yst) 2432
    (mainUnequalState1_canonical yst hx1 hx2) (by decide) (by decide)

private theorem mainUnequalState1_numerator (yst : EvmState) :
    fp2At (mainUnequalState1 yst) 2304 = fp2At (mainUnequalState0 yst) 2304 := by
  unfold mainUnequalState1
  exact fp2SubFinalState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)

theorem mainUnequalState2_numerator (yst : EvmState) :
    fp2At (mainUnequalState2 yst) 2304 = fp2At (mainUnequalState0 yst) 2304 := by
  unfold mainUnequalState2
  exact (fp2InvFinalState_fp2At_before_out_high _ _ _ _
    (by decide) (by decide) (by decide) (by decide)).trans
      (mainUnequalState1_numerator yst)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
