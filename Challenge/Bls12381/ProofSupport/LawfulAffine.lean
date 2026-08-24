import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option warningAsError true

/-!
# Lawful affine short-Weierstrass arithmetic

This module is the inverse-proof-visible mathematical boundary used by the
BLS12-381 challenge family.  It deliberately does not refine to the pinned
`Fin p` curve operations: those operations call the opaque partial
`FF.modInv.go`, whose inverse law is unavailable to Lean.  Concrete wire
adapters instead transport coordinates through the lawful `ZMod` field and
are checked against EIP-2537 vectors.

## Upstream resolution

This local layer is a reproducible EIP-correct bridge, validated by field
properties and official vectors; it is not the preferred permanent home for
curve semantics.  The ideal fix is to upstream a terminating, proof-visible
modular inverse and cancellation theorems into `evm-semantics`, together with
generic affine on-curve and group-law correctness.  After updating the pinned
dependency, this adapter should be proved equivalent to, and then replaced by,
that canonical upstream semantics.  Until then, the opaque `partial def
FF.modInv.go` prevents a kernel proof connecting the pinned affine formulas to
field inverse laws.
-/

namespace Challenge.Bls12381.ProofSupport.LawfulAffine

/-- A short-Weierstrass curve `y² = x³ + a*x + b`. -/
structure Curve (F : Type) where
  a : F
  b : F

/-- An affine point, with infinity represented explicitly. -/
inductive Point (F : Type) where
  | infinity
  | affine (x y : F)
deriving Inhabited, DecidableEq

variable {F : Type} [Field F] [DecidableEq F]

/-- Mathematical curve membership.  Infinity belongs to every curve. -/
def OnCurve (curve : Curve F) : Point F → Prop
  | .infinity => True
  | .affine x y => y ^ 2 = x ^ 3 + curve.a * x + curve.b

/-- Affine negation. -/
def neg : Point F → Point F
  | .infinity => .infinity
  | .affine x y => .affine x (-y)

/-- Lawful affine doubling, with the vertical-tangent branch explicit. -/
def double (curve : Curve F) : Point F → Point F
  | .infinity => .infinity
  | .affine x y =>
      if y = 0 then .infinity
      else
        let slope := (3 * x ^ 2 + curve.a) / (2 * y)
        let x' := slope ^ 2 - 2 * x
        let y' := slope * (x - x') - y
        .affine x' y'

/-- Naive lawful affine addition.  The branch order exposes identity, equal,
opposite/vertical, and general cases without ever dividing by zero. -/
def add (curve : Curve F) : Point F → Point F → Point F
  | .infinity, right => right
  | left, .infinity => left
  | .affine x₁ y₁, .affine x₂ y₂ =>
      if x₁ = x₂ then
        if y₁ + y₂ = 0 then .infinity
        else double curve (.affine x₁ y₁)
      else
        let slope := (y₂ - y₁) / (x₂ - x₁)
        let x₃ := slope ^ 2 - x₁ - x₂
        let y₃ := slope * (x₁ - x₃) - y₁
        .affine x₃ y₃

@[simp] theorem infinity_add (curve : Curve F) (point : Point F) :
    add curve .infinity point = point := by
  cases point <;> rfl

@[simp] theorem add_infinity (curve : Curve F) (point : Point F) :
    add curve point .infinity = point := by
  cases point <;> rfl

@[simp] theorem double_infinity (curve : Curve F) :
    double curve .infinity = .infinity := rfl

@[simp] theorem double_y_zero (curve : Curve F) (x : F) :
    double curve (.affine x 0) = .infinity := by
  simp [double]

omit [DecidableEq F] in
@[simp] theorem neg_infinity : neg (.infinity : Point F) = .infinity := rfl

omit [DecidableEq F] in
@[simp] theorem neg_affine (x y : F) :
    neg (.affine x y) = .affine x (-y) := rfl

@[simp] theorem add_opposite (curve : Curve F) (x y : F) :
    add curve (.affine x y) (.affine x (-y)) = .infinity := by
  simp [add]

theorem add_self_of_sum_ne_zero (curve : Curve F) (x y : F)
    (hsum : y + y ≠ 0) :
    add curve (.affine x y) (.affine x y) =
      double curve (.affine x y) := by
  simp [add, hsum]

theorem add_of_x_ne (curve : Curve F) (x₁ y₁ x₂ y₂ : F)
    (hx : x₁ ≠ x₂) :
    add curve (.affine x₁ y₁) (.affine x₂ y₂) =
      let slope := (y₂ - y₁) / (x₂ - x₁)
      let x₃ := slope ^ 2 - x₁ - x₂
      let y₃ := slope * (x₁ - x₃) - y₁
      .affine x₃ y₃ := by
  simp [add, hx]

omit [DecidableEq F] in
@[simp] theorem onCurve_infinity (curve : Curve F) :
    OnCurve curve .infinity := trivial

omit [DecidableEq F] in
theorem onCurve_neg (curve : Curve F) (point : Point F) :
    OnCurve curve point → OnCurve curve (neg point) := by
  cases point with
  | infinity => simp [OnCurve]
  | affine x y =>
      intro h
      simpa [OnCurve] using h

private theorem onCurve_double_affine (curve : Curve F) (x y : F)
    (h2 : (2 : F) ≠ 0)
    (hcurve : OnCurve curve (.affine x y)) :
    OnCurve curve (double curve (.affine x y)) := by
  by_cases hy : y = 0
  · simp [double, hy, OnCurve]
  · simp only [double, hy, ↓reduceIte]
    simp only [OnCurve] at hcurve ⊢
    let slope := (3 * x ^ 2 + curve.a) / (2 * y)
    have hdenom : 2 * y ≠ 0 := mul_ne_zero h2 hy
    have hslope : slope * (2 * y) = 3 * x ^ 2 + curve.a := by
      exact div_mul_cancel₀ _ hdenom
    have ha : curve.a = slope * (2 * y) - 3 * x ^ 2 := by
      linear_combination -hslope
    have hb : curve.b = y ^ 2 - x ^ 3 - curve.a * x := by
      linear_combination -hcurve
    change
      let x' := slope ^ 2 - 2 * x
      let y' := slope * (x - x') - y
      y' ^ 2 = x' ^ 3 + curve.a * x' + curve.b
    dsimp only
    rw [hb, ha]
    ring

theorem onCurve_double (curve : Curve F) (point : Point F) :
    (2 : F) ≠ 0 → OnCurve curve point →
      OnCurve curve (double curve point) := by
  cases point with
  | infinity => simp [OnCurve, double]
  | affine x y => exact onCurve_double_affine curve x y

omit [DecidableEq F] in
private theorem equal_y_of_onCurve_of_sum_ne_zero (curve : Curve F)
    (x y₁ y₂ : F)
    (h₁ : OnCurve curve (.affine x y₁))
    (h₂ : OnCurve curve (.affine x y₂))
    (hsum : y₁ + y₂ ≠ 0) : y₁ = y₂ := by
  simp only [OnCurve] at h₁ h₂
  have hsq : y₁ ^ 2 = y₂ ^ 2 := h₁.trans h₂.symm
  have hfactor : (y₁ - y₂) * (y₁ + y₂) = 0 := by
    calc
      (y₁ - y₂) * (y₁ + y₂) = y₁ ^ 2 - y₂ ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  rcases mul_eq_zero.mp hfactor with hdiff | hsum'
  · exact sub_eq_zero.mp hdiff
  · exact (hsum hsum').elim

private theorem onCurve_add_general (curve : Curve F)
    (x₁ y₁ x₂ y₂ : F)
    (h₁ : OnCurve curve (.affine x₁ y₁))
    (h₂ : OnCurve curve (.affine x₂ y₂))
    (hx : x₁ ≠ x₂) :
    OnCurve curve (add curve (.affine x₁ y₁) (.affine x₂ y₂)) := by
  simp only [add, hx, ↓reduceIte, OnCurve]
  simp only [OnCurve] at h₁ h₂
  let slope := (y₂ - y₁) / (x₂ - x₁)
  have hdenom : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr hx.symm
  have hslope : slope * (x₂ - x₁) = y₂ - y₁ := by
    exact div_mul_cancel₀ _ hdenom
  have hy₂ : y₂ = y₁ + slope * (x₂ - x₁) := by
    linear_combination -hslope
  have hrelation :
      (x₂ - x₁) *
        (curve.a - (2 * y₁ * slope + slope ^ 2 * (x₂ - x₁) -
          (x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2))) = 0 := by
    rw [hy₂] at h₂
    calc
      _ = (x₂ ^ 3 + curve.a * x₂ + curve.b -
            (x₁ ^ 3 + curve.a * x₁ + curve.b)) -
          ((y₁ + slope * (x₂ - x₁)) ^ 2 - y₁ ^ 2) := by ring
      _ = 0 := by rw [← h₂, ← h₁]; ring
  have ha : curve.a =
      2 * y₁ * slope + slope ^ 2 * (x₂ - x₁) -
        (x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2) := by
    rcases mul_eq_zero.mp hrelation with hzero | hzero
    · exact (hdenom hzero).elim
    · exact sub_eq_zero.mp hzero
  have hb : curve.b = y₁ ^ 2 - x₁ ^ 3 - curve.a * x₁ := by
    linear_combination -h₁
  change
    let x₃ := slope ^ 2 - x₁ - x₂
    let y₃ := slope * (x₁ - x₃) - y₁
    y₃ ^ 2 = x₃ ^ 3 + curve.a * x₃ + curve.b
  dsimp only
  rw [hb, ha]
  ring

theorem onCurve_add (curve : Curve F) (left right : Point F) :
    (2 : F) ≠ 0 → OnCurve curve left → OnCurve curve right →
      OnCurve curve (add curve left right) := by
  cases left with
  | infinity => simp [OnCurve]
  | affine x₁ y₁ =>
      cases right with
      | infinity => simp [OnCurve]
      | affine x₂ y₂ =>
          intro h2 h₁ h₂
          by_cases hx : x₁ = x₂
          · subst x₂
            by_cases hsum : y₁ + y₂ = 0
            · simp [add, hsum, OnCurve]
            · have hy : y₁ = y₂ :=
                equal_y_of_onCurve_of_sum_ne_zero curve x₁ y₁ y₂ h₁ h₂ hsum
              subst y₂
              simpa [add, hsum] using
                onCurve_double curve (.affine x₁ y₁) h2 h₁
          · exact onCurve_add_general curve x₁ y₁ x₂ y₂ h₁ h₂ hx

end Challenge.Bls12381.ProofSupport.LawfulAffine
