import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainDoubleArithmetic
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvCorrect

set_option warningAsError true

/-! # Lawful inverse phase of frozen G2ADD doubling -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem mainDoubleState4_canonical (yst : EvmState)
    (hy : Fp2.Canonical (fp2At (mainValidatedState yst) 128)) :
    Fp2.Canonical (fp2At (mainDoubleState4 yst) 2560) := by
  have hden := mainDoubleState3_canonical yst hy
  unfold mainDoubleState4
  rw [fp2InvFinalState_eq_recovered _ _ _ hden
    (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact canonical_fp2InvRecovered hden

theorem mainDoubleState4_toLawful (yst : EvmState)
    (hy : Fp2.Canonical (fp2At (mainValidatedState yst) 128)) :
    Fp2.toLawful (fp2At (mainDoubleState4 yst) 2560) =
      (2 * Fp2.toLawful (fp2At (mainValidatedState yst) 128))⁻¹ := by
  have h := fp2InvFinalState_toLawful
    (mainDoubleState3 yst) (2560 : U256) 2432
    (mainDoubleState3_canonical yst hy)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [mainDoubleState3_toLawful yst hy] at h
  simpa only [mainDoubleState4] using h

theorem mainDoubleInvNorm_hi_lt (yst : EvmState)
    (hy : Fp2.Canonical (fp2At (mainValidatedState yst) 128)) :
    (fp2InvNorm (mainDoubleState3 yst) 2432).1.toNat < 2 ^ 128 := by
  exact fp2InvNorm_hi_lt_of_input (mainDoubleState3 yst) 2432
    (mainDoubleState3_canonical yst hy) (by decide) (by decide)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
