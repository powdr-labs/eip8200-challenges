import Challenge.Bls12381.ProofSupport.MapPolynomialLawful
import Challenge.Bls12381.ProofSupport.MapToG2IsogenyIdentity
import Mathlib.Tactic.FieldSimp

set_option warningAsError true

/-! # Lawful refinement of the G2 3-isogeny -/

namespace Challenge.Bls12381.ProofSupport.MapToG2

open Challenge.Bls12381.ProofSupport

/-- The RFC 3-isogeny maps every projective point on the isogenous curve to
a lawful G2 point; either rational pole maps to infinity. -/
theorem iso3_onCurve (numerator denominator y : Field)
    (hcurve : y ^ 2 * denominator ^ 3 =
      numerator ^ 3 + isoA * numerator * denominator ^ 2 +
        isoB * denominator ^ 3) :
    G2Affine.OnCurve (iso3 numerator denominator y) := by
  let values := iso3Components numerator denominator
  let xDenominator := values.xDen * denominator
  unfold iso3
  change G2Affine.OnCurve
    (if xDenominator = 0 ∨ values.yDen = 0 then G2Affine.infinity
      else .affine (values.xNum / xDenominator)
        (y * values.yNum / values.yDen))
  by_cases hpole : xDenominator = 0 ∨ values.yDen = 0
  · rw [if_pos hpole]
    trivial
  · rw [if_neg hpole]
    simp only [G2Affine.OnCurve, G2Affine.curve, LawfulAffine.OnCurve]
    have hxDenominator : xDenominator ≠ 0 := fun h => hpole (Or.inl h)
    have hyDenominator : values.yDen ≠ 0 := fun h => hpole (Or.inr h)
    have hdenominator : denominator ≠ 0 := by
      intro h
      apply hxDenominator
      simp [xDenominator, h]
    let x := numerator / denominator
    let xn := MapPolynomial.eval kXNum x
    let xd := MapPolynomial.eval kXDen x
    let yn := MapPolynomial.eval kYNum x
    let yd := MapPolynomial.eval kYDen x
    have hxn := MapPolynomial.evalHom_eq_scaled_eval kXNum
      numerator denominator
      (by
        intro hzero
        have hlength := kXNum_length
        rw [hzero] at hlength
        norm_num at hlength) hdenominator
    have hxd := MapPolynomial.evalHom_eq_scaled_eval kXDen
      numerator denominator
      (by
        intro hzero
        have hlength := kXDen_length
        rw [hzero] at hlength
        norm_num at hlength) hdenominator
    have hyn := MapPolynomial.evalHom_eq_scaled_eval kYNum
      numerator denominator
      (by
        intro hzero
        have hlength := kYNum_length
        rw [hzero] at hlength
        norm_num at hlength) hdenominator
    have hyd := MapPolynomial.evalHom_eq_scaled_eval kYDen
      numerator denominator
      (by
        intro hzero
        have hlength := kYDen_length
        rw [hzero] at hlength
        norm_num at hlength) hdenominator
    simp only [kXNum_length, kXDen_length, kYNum_length, kYDen_length,
      Nat.reduceSubDiff] at hxn hxd hyn hyd
    change values.xNum = denominator ^ 3 * xn at hxn
    change values.xDen = denominator ^ 2 * xd at hxd
    change values.yNum = denominator ^ 3 * yn at hyn
    change values.yDen = denominator ^ 3 * yd at hyd
    have hxdNonzero : xd ≠ 0 := by
      intro hzero
      apply hxDenominator
      dsimp only [xDenominator]
      rw [hxd, hzero]
      simp
    have hydNonzero : yd ≠ 0 := by
      intro hzero
      apply hyDenominator
      rw [hyd, hzero]
      simp
    have hxRatio : values.xNum / xDenominator = xn / xd := by
      dsimp only [xDenominator]
      rw [hxn, hxd]
      field_simp
    have hyRatio : y * values.yNum / values.yDen = y * yn / yd := by
      rw [hyn, hyd]
      field_simp
    have hnumerator : denominator * x = numerator := by
      dsimp only [x]
      field_simp
    have hcurveAffine : y ^ 2 = x ^ 3 + isoA * x + isoB := by
      have hscaled : denominator ^ 3 * y ^ 2 =
          denominator ^ 3 * (x ^ 3 + isoA * x + isoB) := by
        rw [← hnumerator] at hcurve
        convert hcurve using 1 <;> ring
      exact mul_left_cancel₀ (pow_ne_zero 3 hdenominator) hscaled
    have hidentity := iso3_affine_identity x
    rw [← hcurveAffine] at hidentity
    rw [hxRatio, hyRatio]
    simp only [zero_mul, add_zero]
    change (y * yn / yd) ^ 2 =
      (xn / xd) ^ 3 + G2Affine.curve.b
    field_simp [hxdNonzero, hydNonzero]
    convert hidentity using 1
    all_goals ring

end Challenge.Bls12381.ProofSupport.MapToG2
