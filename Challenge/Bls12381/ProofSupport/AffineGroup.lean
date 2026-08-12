import Challenge.Bls12381.ProofSupport.LawfulAffine
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option warningAsError true

/-!
# Independent affine group semantics

This proof-only bridge maps the single local `LawfulAffine` boundary into
Mathlib's independently proved affine elliptic-curve group.  It does not
introduce another executable curve hierarchy.
-/

namespace Challenge.Bls12381.ProofSupport.AffineGroup

variable {F : Type} [Field F] [DecidableEq F]

/-- The Mathlib short-Weierstrass curve corresponding to a local curve. -/
def mathCurve (curve : LawfulAffine.Curve F) : WeierstrassCurve F :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := curve.a, a₆ := curve.b }

omit [DecidableEq F] in
theorem mathCurve_discriminant (curve : LawfulAffine.Curve F) :
    (mathCurve curve).toAffine.Δ =
      -16 * (4 * curve.a ^ 3 + 27 * curve.b ^ 2) := by
  simp only [mathCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- A local affine point paired with its curve-membership proof. -/
abbrev Point (curve : LawfulAffine.Curve F) :=
  { point : LawfulAffine.Point F // LawfulAffine.OnCurve curve point }

/-- The local point at infinity with its membership proof. -/
def infinity (curve : LawfulAffine.Curve F) : Point curve :=
  ⟨.infinity, LawfulAffine.onCurve_infinity curve⟩

/-- Curve-preserving local affine addition on proved points. -/
def add (curve : LawfulAffine.Curve F) (h2 : (2 : F) ≠ 0)
    (left right : Point curve) : Point curve :=
  ⟨LawfulAffine.add curve left.1 right.1,
    LawfulAffine.onCurve_add curve left.1 right.1 h2 left.2 right.2⟩

/-- Curve-preserving local affine doubling on proved points. -/
def double (curve : LawfulAffine.Curve F) (h2 : (2 : F) ≠ 0)
    (point : Point curve) : Point curve :=
  ⟨LawfulAffine.double curve point.1,
    LawfulAffine.onCurve_double curve point.1 h2 point.2⟩

omit [DecidableEq F] in
theorem equation_of_onCurve (curve : LawfulAffine.Curve F) {x y : F}
    (hpoint : LawfulAffine.OnCurve curve (.affine x y)) :
    (mathCurve curve).toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simpa [mathCurve, LawfulAffine.OnCurve] using hpoint

/-- Map a locally proved on-curve point into Mathlib's independent point
group. -/
def toMathlib (curve : LawfulAffine.Curve F)
    [WeierstrassCurve.IsElliptic (mathCurve curve)] :
    Point curve → (mathCurve curve).toAffine.Point
  | ⟨.infinity, _⟩ => 0
  | ⟨.affine _ _, hpoint⟩ =>
      WeierstrassCurve.Affine.Point.mk (equation_of_onCurve curve hpoint)

omit [DecidableEq F] in
/-- The proof-only bridge retains the complete local affine point. -/
theorem toMathlib_injective (curve : LawfulAffine.Curve F)
    [WeierstrassCurve.IsElliptic (mathCurve curve)] :
    Function.Injective (toMathlib curve) := by
  rintro ⟨left, hleft⟩ ⟨right, hright⟩ heq
  apply Subtype.ext
  cases left with
  | infinity =>
      cases right with
      | infinity => rfl
      | affine x y => simp [toMathlib, WeierstrassCurve.Affine.Point.mk] at heq
  | affine x₁ y₁ =>
      cases right with
      | infinity => simp [toMathlib, WeierstrassCurve.Affine.Point.mk] at heq
      | affine x₂ y₂ =>
          simp only [toMathlib, WeierstrassCurve.Affine.Point.mk] at heq
          injection heq with hx hy
          simp [hx, hy]

omit [DecidableEq F] in
@[simp] theorem toMathlib_infinity (curve : LawfulAffine.Curve F)
    [WeierstrassCurve.IsElliptic (mathCurve curve)] :
    toMathlib curve (infinity curve) = 0 := rfl

theorem toMathlib_add (curve : LawfulAffine.Curve F) (h2 : (2 : F) ≠ 0)
    [WeierstrassCurve.IsElliptic (mathCurve curve)]
    (left right : Point curve) :
    toMathlib curve (add curve h2 left right) =
      toMathlib curve left + toMathlib curve right := by
  rcases left with ⟨left, hleft⟩
  rcases right with ⟨right, hright⟩
  cases left with
  | infinity => simp [add, toMathlib]
  | affine x₁ y₁ =>
      cases right with
      | infinity => simp [add, toMathlib]
      | affine x₂ y₂ =>
          have hleftEq := equation_of_onCurve curve hleft
          have hrightEq := equation_of_onCurve curve hright
          by_cases hx : x₁ = x₂
          · subst x₂
            by_cases hsum : y₁ + y₂ = 0
            · have hneg : y₁ = (mathCurve curve).toAffine.negY x₁ y₂ := by
                simp only [WeierstrassCurve.Affine.negY, mathCurve,
                  zero_mul, sub_zero]
                linear_combination hsum
              simp only [add, LawfulAffine.add, if_pos, hsum,
                toMathlib]
              simpa only [WeierstrassCurve.Affine.Point.mk] using
                (WeierstrassCurve.Affine.Point.add_of_Y_eq
                  (W := (mathCurve curve).toAffine) rfl hneg).symm
            · have hneg : y₁ ≠ (mathCurve curve).toAffine.negY x₁ y₂ := by
                intro h
                apply hsum
                simp only [WeierstrassCurve.Affine.negY, mathCurve,
                  zero_mul, sub_zero] at h
                linear_combination h
              have hy : y₁ = y₂ :=
                WeierstrassCurve.Affine.Y_eq_of_Y_ne
                  hleftEq hrightEq rfl hneg
              subst y₂
              have hyZero : y₁ ≠ 0 := by
                intro h
                apply hsum
                simp [h]
              simp only [add, LawfulAffine.add, if_pos, hsum, toMathlib,
                LawfulAffine.double, hyZero, if_false,
                WeierstrassCurve.Affine.Point.mk]
              rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
                (W := (mathCurve curve).toAffine) hneg]
              have hslope :
                  (mathCurve curve).toAffine.slope x₁ x₁ y₁ y₁ =
                    (3 * x₁ ^ 2 + curve.a) / (2 * y₁) := by
                rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
                simp only [mathCurve, zero_mul, sub_zero,
                  WeierstrassCurve.Affine.negY]
                congr 1 <;> ring
              congr 1 <;> rw [hslope] <;>
                simp [mathCurve,
                  WeierstrassCurve.Affine.addX,
                  WeierstrassCurve.Affine.addY,
                  WeierstrassCurve.Affine.negAddY,
                  WeierstrassCurve.Affine.negY] <;> ring
          · have hslope : (y₂ - y₁) / (x₂ - x₁) =
                (y₁ - y₂) / (x₁ - x₂) := by
              rw [show y₂ - y₁ = -(y₁ - y₂) by ring,
                show x₂ - x₁ = -(x₁ - x₂) by ring,
                neg_div_neg_eq]
            simp only [add, LawfulAffine.add, hx, if_false, toMathlib,
              WeierstrassCurve.Affine.Point.mk]
            rw [WeierstrassCurve.Affine.Point.add_of_X_ne
              (W := (mathCurve curve).toAffine) hx]
            congr 1 <;> rw [hslope] <;>
              simp [mathCurve,
                WeierstrassCurve.Affine.slope_of_X_ne hx,
                WeierstrassCurve.Affine.addX,
                WeierstrassCurve.Affine.addY,
                WeierstrassCurve.Affine.negAddY,
                WeierstrassCurve.Affine.negY]
            ring

theorem toMathlib_double (curve : LawfulAffine.Curve F)
    (h2 : (2 : F) ≠ 0)
    [WeierstrassCurve.IsElliptic (mathCurve curve)]
    (point : Point curve) :
    toMathlib curve (double curve h2 point) =
      toMathlib curve point + toMathlib curve point := by
  rw [← toMathlib_add curve h2 point point]
  congr
  apply Subtype.ext
  rcases point with ⟨point, hpoint⟩
  cases point with
  | infinity => rfl
  | affine x y =>
      simp only [add, LawfulAffine.add]
      by_cases hy : y = 0
      · subst y
        simp [double, LawfulAffine.double]
      · have hsum : y + y ≠ 0 := by
          intro hzero
          have : (2 : F) * y = 0 := by
            simpa [two_mul] using hzero
          rcases mul_eq_zero.mp this with htwo | hy'
          · exact h2 htwo
          · exact hy hy'
        simp [double, LawfulAffine.double, hsum]

end Challenge.Bls12381.ProofSupport.AffineGroup
