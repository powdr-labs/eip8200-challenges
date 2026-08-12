import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainUnequalInverse
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulHighLawful
import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteUnequalExec

set_option warningAsError true

/-! # Lawful lambda endpoint of frozen G2ADD unequal addition -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem mainUnequalFinalState_canonical (yst : EvmState)
    (hx1 : Fp2.Canonical (fp2At (mainValidatedState yst) 0))
    (hy1 : Fp2.Canonical (fp2At (mainValidatedState yst) 128))
    (hx2 : Fp2.Canonical (fp2At (mainValidatedState yst) 256))
    (hy2 : Fp2.Canonical (fp2At (mainValidatedState yst) 384)) :
    Fp2.Canonical (fp2At (mainUnequalFinalState yst) 2048) := by
  unfold mainUnequalFinalState
  apply fp2MulFinalState_canonical_of_high_after_out
  · rw [mainUnequalState2_numerator]
    exact mainUnequalState0_canonical yst hy1 hy2
  · exact mainUnequalState2_canonical yst hx1 hx2
  all_goals decide

theorem mainUnequalFinalState_toLawful (yst : EvmState)
    (hx1 : Fp2.Canonical (fp2At (mainValidatedState yst) 0))
    (hy1 : Fp2.Canonical (fp2At (mainValidatedState yst) 128))
    (hx2 : Fp2.Canonical (fp2At (mainValidatedState yst) 256))
    (hy2 : Fp2.Canonical (fp2At (mainValidatedState yst) 384)) :
    Fp2.toLawful (fp2At (mainUnequalFinalState yst) 2048) =
      (Fp2.toLawful (fp2At (mainValidatedState yst) 384) -
        Fp2.toLawful (fp2At (mainValidatedState yst) 128)) /
      (Fp2.toLawful (fp2At (mainValidatedState yst) 256) -
        Fp2.toLawful (fp2At (mainValidatedState yst) 0)) := by
  have hnum : Fp2.Canonical (fp2At (mainUnequalState2 yst) 2304) := by
    rw [mainUnequalState2_numerator]
    exact mainUnequalState0_canonical yst hy1 hy2
  have h := fp2MulFinalState_toLawful_mul_of_high_after_out
    (mainUnequalState2 yst) (2048 : U256) 2304 2560 hnum
    (mainUnequalState2_canonical yst hx1 hx2)
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [mainUnequalState2_numerator, mainUnequalState0_toLawful yst hy1 hy2,
    mainUnequalState2_toLawful yst hx1 hx2] at h
  simpa only [mainUnequalFinalState, div_eq_mul_inv] using h

theorem step_mainUnequalBody_canonical (yst : EvmState)
    (hx1 : Fp2.Canonical (fp2At (mainValidatedState yst) 0))
    (hx2 : Fp2.Canonical (fp2At (mainValidatedState yst) 256)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterFiniteXEq2 yst) mainUnequalBody []
      (mainUnequalFinalState yst) .normal :=
  step_mainUnequalBody yst (mainUnequalInvNorm_hi_lt yst hx1 hx2)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
