import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainDoubleInverse
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvPreservation
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulHighLawful
import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteDoubleExec

set_option warningAsError true

/-! # Lawful lambda endpoint of frozen G2ADD doubling -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private theorem mainDoubleState3_numerator (yst : EvmState) :
    fp2At (mainDoubleState3 yst) 2304 = fp2At (mainDoubleState2 yst) 2304 := by
  unfold mainDoubleState3
  exact fp2AddContractState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)

theorem mainDoubleState4_numerator (yst : EvmState) :
    fp2At (mainDoubleState4 yst) 2304 = fp2At (mainDoubleState2 yst) 2304 := by
  unfold mainDoubleState4
  exact (fp2InvFinalState_fp2At_before_out_high _ _ _ _
    (by decide) (by decide) (by decide) (by decide)).trans
      (mainDoubleState3_numerator yst)

theorem mainDoubleFinalState_canonical (yst : EvmState)
    (hx : Fp2.Canonical (fp2At (mainValidatedState yst) 0))
    (hy : Fp2.Canonical (fp2At (mainValidatedState yst) 128)) :
    Fp2.Canonical (fp2At (mainDoubleFinalState yst) 2048) := by
  unfold mainDoubleFinalState
  apply fp2MulFinalState_canonical_of_high_after_out
  · rw [mainDoubleState4_numerator]
    exact mainDoubleState2_canonical yst hx
  · exact mainDoubleState4_canonical yst hy
  all_goals decide

theorem mainDoubleFinalState_toLawful (yst : EvmState)
    (hx : Fp2.Canonical (fp2At (mainValidatedState yst) 0))
    (hy : Fp2.Canonical (fp2At (mainValidatedState yst) 128)) :
    Fp2.toLawful (fp2At (mainDoubleFinalState yst) 2048) =
      (3 * Fp2.toLawful (fp2At (mainValidatedState yst) 0) ^ 2) /
        (2 * Fp2.toLawful (fp2At (mainValidatedState yst) 128)) := by
  have hnum : Fp2.Canonical (fp2At (mainDoubleState4 yst) 2304) := by
    rw [mainDoubleState4_numerator]
    exact mainDoubleState2_canonical yst hx
  have h := fp2MulFinalState_toLawful_mul_of_high_after_out
    (mainDoubleState4 yst) (2048 : U256) 2304 2560 hnum
    (mainDoubleState4_canonical yst hy)
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [mainDoubleState4_numerator, mainDoubleState2_toLawful yst hx,
    mainDoubleState4_toLawful yst hy] at h
  simpa only [mainDoubleFinalState, div_eq_mul_inv] using h

theorem step_mainDoubleBody_canonical (yst : EvmState)
    (hy : Fp2.Canonical (fp2At (mainValidatedState yst) 128)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterDoubleYZero yst) mainDoubleBody []
      (mainDoubleFinalState yst) .normal :=
  step_mainDoubleBody yst (mainDoubleInvNorm_hi_lt yst hy)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
