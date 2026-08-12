import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainPointLawful

set_option warningAsError true

/-! # Lawful meaning of the frozen G2ADD curve-rejection conditions -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private theorem u256_zero_eq : (0 : U256) = 0#256 := by
  apply BitVec.eq_of_toNat_eq
  decide

private theorem mainCurve1Result_cases (yst : EvmState) :
    mainCurve1Result yst = 0 ∨ mainCurve1Result yst = 1 := by
  unfold mainCurve1Result onCurveResult
  exact fp2EqValue_zero_or_one _ _ _

private theorem mainCurve2Result_cases (yst : EvmState) :
    mainCurve2Result yst = 0 ∨ mainCurve2Result yst = 1 := by
  unfold mainCurve2Result onCurveResult
  exact fp2EqValue_zero_or_one _ _ _

theorem mainCurve1ConditionValue_eq_zero_iff (yst : EvmState)
    (hx : Fp2.Canonical (sourceFp2 yst 0))
    (hy : Fp2.Canonical (sourceFp2 yst 128)) :
    mainCurve1ConditionValue yst = 0 ↔
      mainInf1 yst ≠ 0 ∨ G2Affine.OnCurve (.affine
        (Fp2.toLawful (sourceFp2 yst 0))
        (Fp2.toLawful (sourceFp2 yst 128))) := by
  have hone := mainCurve1Result_eq_one_iff yst hx hy
  rcases mainCurve1Result_cases yst with hzero | hone'
  · have hzero' : mainCurve1Result yst = 0#256 :=
      hzero.trans u256_zero_eq
    have hnot : ¬G2Affine.OnCurve (.affine
        (Fp2.toLawful (sourceFp2 yst 0))
        (Fp2.toLawful (sourceFp2 yst 128))) := by
      intro hcurve
      have := hone.mpr hcurve
      exact (by decide : (0 : U256) ≠ 1) (hzero.symm.trans this)
    by_cases hinf : mainInf1 yst = 0
    · simp [mainCurve1ConditionValue, hinf, hzero', hnot, b2w]
    · have hinf' : mainInf1 yst ≠ 0#256 := by
        simpa only [← u256_zero_eq] using hinf
      simp [mainCurve1ConditionValue, hinf', hzero', hnot, b2w]
  · have hcurve := hone.mp hone'
    have hne : mainCurve1Result yst ≠ 0#256 := by
      intro hzero
      have hzero' : mainCurve1Result yst = (0 : U256) :=
        hzero.trans u256_zero_eq.symm
      exact (by decide : (0 : U256) ≠ 1) (hzero'.symm.trans hone')
    simp [mainCurve1ConditionValue, hcurve, hne, b2w]

theorem mainCurve2ConditionValue_eq_zero_iff (yst : EvmState)
    (hx : Fp2.Canonical (sourceFp2 yst 256))
    (hy : Fp2.Canonical (sourceFp2 yst 384)) :
    mainCurve2ConditionValue yst = 0 ↔
      mainInf2 yst ≠ 0 ∨ G2Affine.OnCurve (.affine
        (Fp2.toLawful (sourceFp2 yst 256))
        (Fp2.toLawful (sourceFp2 yst 384))) := by
  have hone := mainCurve2Result_eq_one_iff yst hx hy
  rcases mainCurve2Result_cases yst with hzero | hone'
  · have hzero' : mainCurve2Result yst = 0#256 :=
      hzero.trans u256_zero_eq
    have hnot : ¬G2Affine.OnCurve (.affine
        (Fp2.toLawful (sourceFp2 yst 256))
        (Fp2.toLawful (sourceFp2 yst 384))) := by
      intro hcurve
      have := hone.mpr hcurve
      exact (by decide : (0 : U256) ≠ 1) (hzero.symm.trans this)
    by_cases hinf : mainInf2 yst = 0
    · simp [mainCurve2ConditionValue, hinf, hzero', hnot, b2w]
    · have hinf' : mainInf2 yst ≠ 0#256 := by
        simpa only [← u256_zero_eq] using hinf
      simp [mainCurve2ConditionValue, hinf', hzero', hnot, b2w]
  · have hcurve := hone.mp hone'
    have hne : mainCurve2Result yst ≠ 0#256 := by
      intro hzero
      have hzero' : mainCurve2Result yst = (0 : U256) :=
        hzero.trans u256_zero_eq.symm
      exact (by decide : (0 : U256) ≠ 1) (hzero'.symm.trans hone')
    simp [mainCurve2ConditionValue, hcurve, hne, b2w]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
