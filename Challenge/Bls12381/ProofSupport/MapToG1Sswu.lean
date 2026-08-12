import Challenge.Bls12381.ProofSupport.MapToG1SqrtRatio

set_option warningAsError true

/-! # Source G1 simplified SWU refinement -/

namespace Challenge.Bls12381.ProofSupport.MapToG1

/-- The source square-root-ratio implementation discharges the SSWU
dependency, yielding an unconditional projective on-curve theorem. -/
theorem sswuSource_onCurve (u : Field) :
    ProjectiveOnCurve (sswuProjective sqrtRatioSource u) := by
  apply sswuProjective_onCurve_of_valid sqrtRatioSource u
  generalize hnumerator : sswuNumerator u = numerator
  generalize hdenominator : sswuDenominator u = denominator
  have hdenominator' : denominator ≠ 0 := by
    rw [← hdenominator]
    simpa only [sswuDenominator] using
      SswuCore.denominator_ne_zero suite isoA_ne_zero isoZ_ne_zero u
  have hvalid : SqrtRatioValid numerator denominator
      (sqrtRatioSource numerator denominator) :=
    sqrtRatioSource_valid numerator denominator hdenominator'
  exact hvalid

end Challenge.Bls12381.ProofSupport.MapToG1
