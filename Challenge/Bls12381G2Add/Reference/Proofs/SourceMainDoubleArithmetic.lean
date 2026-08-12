import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteInputs
import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveMulLawful

set_option warningAsError true

/-! # Lawful arithmetic setup for frozen G2ADD doubling

The square, numerator, and denominator facts form one small private dependency
chain.  Keeping them together avoids treating each arithmetic observation as a
separate production concept while the expensive `fp2Add` execution graph stays
behind its opaque contract boundary.
-/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem mainDoubleState0_canonical (yst : EvmState)
    (hx : Fp2.Canonical (fp2At (mainValidatedState yst) 0)) :
    Fp2.Canonical (fp2At (mainDoubleState0 yst) 2176) := by
  unfold mainDoubleState0
  apply fp2MulFinalState_canonical_of_low
  · rwa [mainAfterDoubleYZero_fp2At]
  · rwa [mainAfterDoubleYZero_fp2At]
  all_goals decide

theorem mainDoubleState0_toLawful (yst : EvmState)
    (hx : Fp2.Canonical (fp2At (mainValidatedState yst) 0)) :
    Fp2.toLawful (fp2At (mainDoubleState0 yst) 2176) =
      Fp2.toLawful (fp2At (mainValidatedState yst) 0) ^ 2 := by
  have h := fp2MulFinalState_toLawful_mul_of_low
    (mainAfterDoubleYZero yst) (2176 : U256) 0 0
    (by rwa [mainAfterDoubleYZero_fp2At])
    (by rwa [mainAfterDoubleYZero_fp2At])
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  rw [mainAfterDoubleYZero_fp2At] at h
  simpa only [mainDoubleState0, pow_two] using h

private theorem mainDoubleState1_xsq (yst : EvmState) :
    fp2At (mainDoubleState1 yst) 2176 = fp2At (mainDoubleState0 yst) 2176 := by
  unfold mainDoubleState1
  exact fp2AddContractState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)

theorem mainDoubleState1_canonical (yst : EvmState)
    (hx : Fp2.Canonical (fp2At (mainValidatedState yst) 0)) :
    Fp2.Canonical (fp2At (mainDoubleState1 yst) 2304) := by
  rw [mainDoubleState1,
    fp2AddContractState_output_inputs_before _ _ _ _
      (by decide) (by decide) (by decide)]
  exact Fp2.canonical_addSource
    (mainDoubleState0_canonical yst hx) (mainDoubleState0_canonical yst hx)

theorem mainDoubleState1_toLawful (yst : EvmState)
    (hx : Fp2.Canonical (fp2At (mainValidatedState yst) 0)) :
    Fp2.toLawful (fp2At (mainDoubleState1 yst) 2304) =
      2 * Fp2.toLawful (fp2At (mainValidatedState yst) 0) ^ 2 := by
  have hcanonical := mainDoubleState0_canonical yst hx
  rw [mainDoubleState1,
    fp2AddContractState_output_inputs_before _ _ _ _
      (by decide) (by decide) (by decide),
    Fp2.toLawful_addSource hcanonical hcanonical,
    mainDoubleState0_toLawful yst hx]
  ring

private theorem mainDoubleState2_xsq (yst : EvmState) :
    fp2At (mainDoubleState2 yst) 2176 = fp2At (mainDoubleState0 yst) 2176 := by
  unfold mainDoubleState2
  exact (fp2AddContractState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)).trans (mainDoubleState1_xsq yst)

theorem mainDoubleState2_canonical (yst : EvmState)
    (hx : Fp2.Canonical (fp2At (mainValidatedState yst) 0)) :
    Fp2.Canonical (fp2At (mainDoubleState2 yst) 2304) := by
  rw [mainDoubleState2,
    fp2AddContractState_output_inplace_left_before _ _ _
      (by decide) (by decide)]
  exact Fp2.canonical_addSource (mainDoubleState1_canonical yst hx)
    (mainDoubleState1_xsq yst ▸ mainDoubleState0_canonical yst hx)

theorem mainDoubleState2_toLawful (yst : EvmState)
    (hx : Fp2.Canonical (fp2At (mainValidatedState yst) 0)) :
    Fp2.toLawful (fp2At (mainDoubleState2 yst) 2304) =
      3 * Fp2.toLawful (fp2At (mainValidatedState yst) 0) ^ 2 := by
  have hnum := mainDoubleState1_canonical yst hx
  have hsq := mainDoubleState0_canonical yst hx
  have hsq1 : Fp2.Canonical (fp2At (mainDoubleState1 yst) 2176) := by
    rw [mainDoubleState1_xsq]
    exact hsq
  rw [mainDoubleState2,
    fp2AddContractState_output_inplace_left_before _ _ _
      (by decide) (by decide),
    Fp2.toLawful_addSource hnum hsq1,
    mainDoubleState1_toLawful yst hx, mainDoubleState1_xsq,
    mainDoubleState0_toLawful yst hx]
  ring

private theorem mainDoubleState0_y (yst : EvmState) :
    fp2At (mainDoubleState0 yst) 128 = fp2At (mainValidatedState yst) 128 := by
  unfold mainDoubleState0
  exact (fp2MulFinalState_fp2At_before_scratch _ _ _ _ _
    (by decide) (by decide) (by decide) (by decide)).trans
      (mainAfterDoubleYZero_fp2At yst 128)

private theorem mainDoubleState1_y (yst : EvmState) :
    fp2At (mainDoubleState1 yst) 128 = fp2At (mainValidatedState yst) 128 := by
  unfold mainDoubleState1
  exact (fp2AddContractState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)).trans (mainDoubleState0_y yst)

theorem mainDoubleState2_y (yst : EvmState) :
    fp2At (mainDoubleState2 yst) 128 = fp2At (mainValidatedState yst) 128 := by
  unfold mainDoubleState2
  exact (fp2AddContractState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)).trans (mainDoubleState1_y yst)

theorem mainDoubleState3_canonical (yst : EvmState)
    (hy : Fp2.Canonical (fp2At (mainValidatedState yst) 128)) :
    Fp2.Canonical (fp2At (mainDoubleState3 yst) 2432) := by
  rw [mainDoubleState3,
    fp2AddContractState_output_inputs_before _ _ _ _
      (by decide) (by decide) (by decide),
    mainDoubleState2_y]
  exact Fp2.canonical_addSource hy hy

theorem mainDoubleState3_toLawful (yst : EvmState)
    (hy : Fp2.Canonical (fp2At (mainValidatedState yst) 128)) :
    Fp2.toLawful (fp2At (mainDoubleState3 yst) 2432) =
      2 * Fp2.toLawful (fp2At (mainValidatedState yst) 128) := by
  have hinput : Fp2.Canonical (fp2At (mainDoubleState2 yst) 128) := by
    rw [mainDoubleState2_y]
    exact hy
  rw [mainDoubleState3,
    fp2AddContractState_output_inputs_before _ _ _ _
      (by decide) (by decide) (by decide),
    Fp2.toLawful_addSource hinput hinput,
    mainDoubleState2_y]
  ring

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
