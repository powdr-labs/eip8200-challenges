import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainCurveExec

set_option warningAsError true

/-! # Lawful meaning of the frozen G1ADD point-validation conditions -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

private abbrev G1Point :=
  Challenge.Bls12381.ProofSupport.G1Affine.Point

private theorem u256_zero_eq : (0 : U256) = 0#256 := by
  apply BitVec.eq_of_toNat_eq
  decide

def mainAffine1 (yst : EvmState) : G1Point :=
  .affine
    (Challenge.Bls12381.ProofSupport.Fp.value (mainX1 yst))
    (Challenge.Bls12381.ProofSupport.Fp.value (mainY1 yst))

def mainAffine2 (yst : EvmState) : G1Point :=
  .affine
    (Challenge.Bls12381.ProofSupport.Fp.value (mainX2 yst))
    (Challenge.Bls12381.ProofSupport.Fp.value (mainY2 yst))

private theorem curve1_result_eq_one_iff (yst : EvmState)
    (hx : Challenge.Bls12381.ProofSupport.Fp.Canonical (mainX1 yst))
    (hy : Challenge.Bls12381.ProofSupport.Fp.Canonical (mainY1 yst)) :
    mainCurve1Result yst = 1 ↔
      Challenge.Bls12381.ProofSupport.G1Affine.OnCurve (mainAffine1 yst) := by
  simpa [mainCurve1Result, mainAffine1, mainX1, mainY1] using
    onCurveResult_eq_one_iff (mainCurve1ArgsState yst)
      (mainDecodedWord yst 0) (mainDecodedWord yst 32)
      (mainDecodedWord yst 64) (mainDecodedWord yst 96) hx hy

private theorem curve2_result_eq_one_iff (yst : EvmState)
    (hx : Challenge.Bls12381.ProofSupport.Fp.Canonical (mainX2 yst))
    (hy : Challenge.Bls12381.ProofSupport.Fp.Canonical (mainY2 yst)) :
    mainCurve2Result yst = 1 ↔
      Challenge.Bls12381.ProofSupport.G1Affine.OnCurve (mainAffine2 yst) := by
  simpa [mainCurve2Result, mainAffine2, mainX2, mainY2] using
    onCurveResult_eq_one_iff (mainCurve2ArgsState yst)
      (mainDecodedWord yst 128) (mainDecodedWord yst 160)
      (mainDecodedWord yst 192) (mainDecodedWord yst 224) hx hy

theorem mainCurve1ConditionValue_eq_zero_iff (yst : EvmState)
    (hx : Challenge.Bls12381.ProofSupport.Fp.Canonical (mainX1 yst))
    (hy : Challenge.Bls12381.ProofSupport.Fp.Canonical (mainY1 yst)) :
    mainCurve1ConditionValue yst = 0 ↔
      mainInf1 yst ≠ 0#256 ∨
        Challenge.Bls12381.ProofSupport.G1Affine.OnCurve
          (mainAffine1 yst) := by
  have hone := curve1_result_eq_one_iff yst hx hy
  rcases onCurveResult_zero_or_one (mainCurve1ArgsState yst)
      (mainDecodedWord yst 0) (mainDecodedWord yst 32)
      (mainDecodedWord yst 64) (mainDecodedWord yst 96) with hzero | hone'
  · change mainCurve1Result yst = 0 at hzero
    have hzero' : mainCurve1Result yst = 0#256 :=
      hzero.trans u256_zero_eq
    have hnot : ¬Challenge.Bls12381.ProofSupport.G1Affine.OnCurve
        (mainAffine1 yst) := by
      intro hcurve
      have := hone.mpr hcurve
      exact (by decide : (0 : U256) ≠ 1) (hzero.symm.trans this)
    by_cases hinf : mainInf1 yst = 0#256
    · simp [mainCurve1ConditionValue, hinf, hzero', hnot, b2w]
    · simp [mainCurve1ConditionValue, hinf, hzero', hnot, b2w]
  · change mainCurve1Result yst = 1 at hone'
    have hcurve := hone.mp hone'
    have hne : mainCurve1Result yst ≠ 0#256 := by
      intro hzero
      have hzero' : mainCurve1Result yst = (0 : U256) :=
        hzero.trans u256_zero_eq.symm
      exact (by decide : (0 : U256) ≠ 1) (hzero'.symm.trans hone')
    simp [mainCurve1ConditionValue, hcurve, hne, b2w]

theorem mainCurve2ConditionValue_eq_zero_iff (yst : EvmState)
    (hx : Challenge.Bls12381.ProofSupport.Fp.Canonical (mainX2 yst))
    (hy : Challenge.Bls12381.ProofSupport.Fp.Canonical (mainY2 yst)) :
    mainCurve2ConditionValue yst = 0 ↔
      mainInf2 yst ≠ 0#256 ∨
        Challenge.Bls12381.ProofSupport.G1Affine.OnCurve
          (mainAffine2 yst) := by
  have hone := curve2_result_eq_one_iff yst hx hy
  rcases onCurveResult_zero_or_one (mainCurve2ArgsState yst)
      (mainDecodedWord yst 128) (mainDecodedWord yst 160)
      (mainDecodedWord yst 192) (mainDecodedWord yst 224) with hzero | hone'
  · change mainCurve2Result yst = 0 at hzero
    have hzero' : mainCurve2Result yst = 0#256 :=
      hzero.trans u256_zero_eq
    have hnot : ¬Challenge.Bls12381.ProofSupport.G1Affine.OnCurve
        (mainAffine2 yst) := by
      intro hcurve
      have := hone.mpr hcurve
      exact (by decide : (0 : U256) ≠ 1) (hzero.symm.trans this)
    by_cases hinf : mainInf2 yst = 0#256
    · simp [mainCurve2ConditionValue, hinf, hzero', hnot, b2w]
    · simp [mainCurve2ConditionValue, hinf, hzero', hnot, b2w]
  · change mainCurve2Result yst = 1 at hone'
    have hcurve := hone.mp hone'
    have hne : mainCurve2Result yst ≠ 0#256 := by
      intro hzero
      have hzero' : mainCurve2Result yst = (0 : U256) :=
        hzero.trans u256_zero_eq.symm
      exact (by decide : (0 : U256) ≠ 1) (hzero'.symm.trans hone')
    simp [mainCurve2ConditionValue, hcurve, hne, b2w]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
