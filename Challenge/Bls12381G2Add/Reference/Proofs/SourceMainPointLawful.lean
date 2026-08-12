import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainLowMemory

set_option warningAsError true

/-! # Lawful meaning of G2ADD point predicates and curve checks -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private theorem fp2At_afterInf2 (yst : EvmState) (ptr : U256) :
    fp2At (mainAfterInf2Reads yst) ptr = fp2At (mainDecodedState yst) ptr := by
  apply fp2At_eq_of_loads
  all_goals rw [mainAfterInf2Reads_memory]

private theorem fp2At_afterCurve1 (yst : EvmState) (ptr : U256)
    (hptr : ptr.toNat + 128 ≤ 1024) :
    fp2At (mainAfterCurve1 yst) ptr = fp2At (mainDecodedState yst) ptr := by
  apply fp2At_eq_of_loads
  all_goals
    rw [mainAfterCurve1_loadWord_low yst _ (by bv_omega)]
    rfl

theorem mainInf1_zero_or_one (yst : EvmState) :
    mainInf1 yst = 0 ∨ mainInf1 yst = 1 := by
  have h := pointZeroValue_zero_or_one (mainAfterValidationReads yst) 0
  simpa only [mainInf1] using h

theorem mainInf2_zero_or_one (yst : EvmState) :
    mainInf2 yst = 0 ∨ mainInf2 yst = 1 := by
  have h := pointZeroValue_zero_or_one (mainAfterInf1Reads yst) 256
  simpa only [mainInf2] using h

theorem mainInf1_eq_one_iff (yst : EvmState) :
    mainInf1 yst = 1 ↔
      sourceFp2 yst 0 = Challenge.Bls12381.ProofSupport.Fp2.zero ∧
      sourceFp2 yst 128 = Challenge.Bls12381.ProofSupport.Fp2.zero := by
  unfold mainInf1
  rw [pointZeroValue_eq_one_iff]
  rw [fp2WordsAt_eq_zero_iff_fp2At_eq_zero,
    fp2WordsAt_eq_zero_iff_fp2At_eq_zero]
  have hmem := mainAfterValidationReads_memory yst
  have h0 : fp2At (mainAfterValidationReads yst) 0 =
      fp2At (mainDecodedState yst) 0 := by
    apply fp2At_eq_of_loads <;> all_goals rw [hmem]
  have h128 : fp2At (mainAfterValidationReads yst) (BitVec.ofNat 256 128) =
      fp2At (mainDecodedState yst) (BitVec.ofNat 256 128) := by
    apply fp2At_eq_of_loads <;> all_goals rw [hmem]
  unfold sourceFp2
  rw [h0,
    show (0 : U256) + BitVec.ofNat 256 128 = BitVec.ofNat 256 128 by decide,
    h128]
  rw [show (0 : U256) = BitVec.ofNat 256 0 by decide]

theorem mainInf2_eq_one_iff (yst : EvmState) :
    mainInf2 yst = 1 ↔
      sourceFp2 yst 256 = Challenge.Bls12381.ProofSupport.Fp2.zero ∧
      sourceFp2 yst 384 = Challenge.Bls12381.ProofSupport.Fp2.zero := by
  unfold mainInf2
  rw [pointZeroValue_eq_one_iff]
  rw [fp2WordsAt_eq_zero_iff_fp2At_eq_zero,
    fp2WordsAt_eq_zero_iff_fp2At_eq_zero]
  have hmem := mainAfterInf1Reads_memory yst
  have h256 : fp2At (mainAfterInf1Reads yst) 256 =
      fp2At (mainDecodedState yst) 256 := by
    apply fp2At_eq_of_loads <;> all_goals rw [hmem]
  have h384 : fp2At (mainAfterInf1Reads yst) (BitVec.ofNat 256 384) =
      fp2At (mainDecodedState yst) (BitVec.ofNat 256 384) := by
    apply fp2At_eq_of_loads <;> all_goals rw [hmem]
  unfold sourceFp2
  rw [h256,
    show (256 : U256) + BitVec.ofNat 256 128 = BitVec.ofNat 256 384 by decide,
    h384]
  rw [show (256 : U256) = BitVec.ofNat 256 256 by decide]

theorem mainCurve1Result_eq_one_iff (yst : EvmState)
    (hx : Fp2.Canonical (sourceFp2 yst 0))
    (hy : Fp2.Canonical (sourceFp2 yst 128)) :
    mainCurve1Result yst = 1 ↔
      G2Affine.OnCurve (.affine
        (Fp2.toLawful (sourceFp2 yst 0))
        (Fp2.toLawful (sourceFp2 yst 128))) := by
  unfold mainCurve1Result
  have h := onCurveResult_eq_one_iff (mainAfterInf2Reads yst) 0 128
    (by simpa [fp2At_afterInf2, sourceFp2] using hx)
    (by simpa [fp2At_afterInf2, sourceFp2] using hy)
    (by decide) (by decide) (by decide) (by decide)
  simpa [fp2At_afterInf2, sourceFp2] using h

theorem mainCurve2Result_eq_one_iff (yst : EvmState)
    (hx : Fp2.Canonical (sourceFp2 yst 256))
    (hy : Fp2.Canonical (sourceFp2 yst 384)) :
    mainCurve2Result yst = 1 ↔
      G2Affine.OnCurve (.affine
        (Fp2.toLawful (sourceFp2 yst 256))
        (Fp2.toLawful (sourceFp2 yst 384))) := by
  unfold mainCurve2Result
  have h := onCurveResult_eq_one_iff (mainAfterCurve1 yst) 256 384
    (by simpa [fp2At_afterCurve1, sourceFp2] using hx)
    (by simpa [fp2At_afterCurve1, sourceFp2] using hy)
    (by decide) (by decide) (by decide) (by decide)
  simpa [fp2At_afterCurve1, sourceFp2] using h

private theorem mainCurve1Result_zero_or_one (yst : EvmState) :
    mainCurve1Result yst = 0 ∨ mainCurve1Result yst = 1 := by
  unfold mainCurve1Result onCurveResult
  exact fp2EqValue_zero_or_one _ _ _

private theorem mainCurve2Result_zero_or_one (yst : EvmState) :
    mainCurve2Result yst = 0 ∨ mainCurve2Result yst = 1 := by
  unfold mainCurve2Result onCurveResult
  exact fp2EqValue_zero_or_one _ _ _

theorem mainCurve1_success_finite (yst : EvmState)
    (hx : Fp2.Canonical (sourceFp2 yst 0))
    (hy : Fp2.Canonical (sourceFp2 yst 128))
    (hinf : mainInf1 yst = 0)
    (hcurve : mainCurve1ConditionValue yst = 0) :
    G2Affine.OnCurve (.affine
      (Fp2.toLawful (sourceFp2 yst 0))
      (Fp2.toLawful (sourceFp2 yst 128))) := by
  have hresult : mainCurve1Result yst = 1 := by
    rcases mainCurve1Result_zero_or_one yst with hz | ho
    · unfold mainCurve1ConditionValue b2w at hcurve
      simp [hinf, hz] at hcurve
    · exact ho
  exact (mainCurve1Result_eq_one_iff yst hx hy).mp hresult

theorem mainCurve2_success_finite (yst : EvmState)
    (hx : Fp2.Canonical (sourceFp2 yst 256))
    (hy : Fp2.Canonical (sourceFp2 yst 384))
    (hinf : mainInf2 yst = 0)
    (hcurve : mainCurve2ConditionValue yst = 0) :
    G2Affine.OnCurve (.affine
      (Fp2.toLawful (sourceFp2 yst 256))
      (Fp2.toLawful (sourceFp2 yst 384))) := by
  have hresult : mainCurve2Result yst = 1 := by
    rcases mainCurve2Result_zero_or_one yst with hz | ho
    · unfold mainCurve2ConditionValue b2w at hcurve
      simp [hinf, hz] at hcurve
    · exact ho
  exact (mainCurve2Result_eq_one_iff yst hx hy).mp hresult

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
