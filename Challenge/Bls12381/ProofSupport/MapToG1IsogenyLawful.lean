import Challenge.Bls12381.ProofSupport.MapToG1IsogenyIdentity
import Challenge.Bls12381.ProofSupport.MapPolynomialLawful
import Mathlib.Tactic.FieldSimp

set_option warningAsError true

/-! # Lawful refinement of the G1 11-isogeny -/

namespace Challenge.Bls12381.ProofSupport.MapToG1

open Challenge.Bls12381.ProofSupport

/-- Homogeneous evaluation agrees with ordinary evaluation at `N/D`, scaled
by the expected denominator power. -/
theorem evalHom_eq_scaled_eval (coefficients : List Field)
    (numerator denominator : Field) (hcoefficients : coefficients ≠ [])
    (hdenominator : denominator ≠ 0) :
    MapPolynomial.evalHom coefficients numerator denominator =
      denominator ^ (coefficients.length - 1) *
        MapPolynomial.eval coefficients (numerator / denominator) :=
  MapPolynomial.evalHom_eq_scaled_eval coefficients numerator denominator
    hcoefficients hdenominator

/-- The RFC 11-isogeny maps every projective point on the isogenous curve to
a lawful G1 point; either rational pole maps to infinity. -/
theorem iso11_onCurve (numerator denominator y : Field)
    (hcurve : y ^ 2 * denominator ^ 3 =
      numerator ^ 3 + isoA * numerator * denominator ^ 2 +
        isoB * denominator ^ 3) :
    G1Affine.OnCurve (iso11 numerator denominator y) := by
  let values := iso11Components numerator denominator
  let xDenominator := values.xDen * denominator
  unfold iso11
  change G1Affine.OnCurve
    (if xDenominator = 0 ∨ values.yDen = 0 then G1Affine.infinity
      else .affine (values.xNum / xDenominator)
        (y * values.yNum / values.yDen))
  by_cases hpole : xDenominator = 0 ∨ values.yDen = 0
  · rw [if_pos hpole]
    trivial
  · rw [if_neg hpole]
    simp only [G1Affine.OnCurve, G1Affine.curve, LawfulAffine.OnCurve]
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
    have hxn := evalHom_eq_scaled_eval kXNum numerator denominator
      (by
        intro hzero
        have hlength := kXNum_length
        rw [hzero] at hlength
        norm_num at hlength) hdenominator
    have hxd := evalHom_eq_scaled_eval kXDen numerator denominator
      (by
        intro hzero
        have hlength := kXDen_length
        rw [hzero] at hlength
        norm_num at hlength) hdenominator
    have hyn := evalHom_eq_scaled_eval kYNum numerator denominator
      (by
        intro hzero
        have hlength := kYNum_length
        rw [hzero] at hlength
        norm_num at hlength) hdenominator
    have hyd := evalHom_eq_scaled_eval kYDen numerator denominator
      (by
        intro hzero
        have hlength := kYDen_length
        rw [hzero] at hlength
        norm_num at hlength) hdenominator
    simp only [kXNum_length, kXDen_length, kYNum_length, kYDen_length,
      Nat.reduceSubDiff] at hxn hxd hyn hyd
    change values.xNum = denominator ^ 11 * xn at hxn
    change values.xDen = denominator ^ 10 * xd at hxd
    change values.yNum = denominator ^ 15 * yn at hyn
    change values.yDen = denominator ^ 15 * yd at hyd
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
    have hidentity := iso11_affine_identity x
    rw [← hcurveAffine] at hidentity
    rw [hxRatio, hyRatio]
    simp only [zero_mul, add_zero]
    change (y * yn / yd) ^ 2 = (xn / xd) ^ 3 + 4
    field_simp [hxdNonzero, hydNonzero]
    convert hidentity using 1
    all_goals ring

end Challenge.Bls12381.ProofSupport.MapToG1
