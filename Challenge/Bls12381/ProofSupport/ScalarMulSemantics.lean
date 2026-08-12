import Challenge.Bls12381.ProofSupport.ScalarMul
import Challenge.Bls12381.ProofSupport.AffineGroup
import Challenge.Bls12381.ProofSupport.AffineGroupBls

set_option warningAsError true

/-!
# Independent group semantics for scalar multiplication

This proof-only module maps the executable binary recursion into Mathlib's
independently proved affine elliptic-curve groups.  Keeping this bridge out of
`ScalarMul` prevents executable MSM and subgroup consumers from importing the
algebraic-geometry stack.
-/

namespace Challenge.Bls12381.ProofSupport.ScalarMul

/-- Map the auditable binary recursion into the independent `nsmul`
semantics of any additive monoid.  The hypotheses deliberately describe the
map boundary rather than assuming group laws for the executable point type. -/
theorem binary_map_nsmul {Point Target : Type} [AddCommMonoid Target]
    (zero : Point) (add : Point → Point → Point) (double : Point → Point)
    (mapPoint : Point → Target)
    (hzero : mapPoint zero = 0)
    (hadd : ∀ left right, mapPoint (add left right) =
      mapPoint left + mapPoint right)
    (hdouble : ∀ point, mapPoint (double point) =
      mapPoint point + mapPoint point)
    (scalar : Nat) (point : Point) :
    mapPoint (binary zero add double scalar point) =
      scalar • mapPoint point := by
  induction scalar using Nat.strong_induction_on generalizing point with
  | h scalar ih =>
      by_cases hscalar : scalar = 0
      · subst scalar
        simpa using hzero
      · by_cases hone : scalar = 1
        · subst scalar
          simp
        rw [binary_step zero add double scalar point hscalar, if_neg hone]
        have hhalf : scalar / 2 < scalar :=
          Nat.div_lt_self (Nat.zero_lt_of_ne_zero hscalar) (by omega)
        by_cases hodd : scalar % 2 = 1
        · rw [if_pos hodd, hadd, ih (scalar / 2) hhalf (double point),
            hdouble]
          have hscalarOdd : scalar = 2 * (scalar / 2) + 1 := by omega
          calc
            (scalar / 2) • (mapPoint point + mapPoint point) + mapPoint point =
                (2 * (scalar / 2) + 1) • mapPoint point := by
              simp only [nsmul_add, add_nsmul, one_nsmul, two_mul]
            _ = scalar • mapPoint point := by rw [← hscalarOdd]
        · have heven : scalar % 2 = 0 := by omega
          rw [if_neg hodd, ih (scalar / 2) hhalf (double point), hdouble]
          have hscalarEven : scalar = 2 * (scalar / 2) := by omega
          calc
            (scalar / 2) • (mapPoint point + mapPoint point) =
                (2 * (scalar / 2)) • mapPoint point := by
              simp only [nsmul_add, two_mul, add_nsmul]
            _ = scalar • mapPoint point := by rw [← hscalarEven]

/-- The local on-curve binary recursion maps to Mathlib's independently
proved affine-group `nsmul`. -/
theorem binary_onCurve_nsmul {F : Type} [Field F] [DecidableEq F]
    (curve : LawfulAffine.Curve F) (h2 : (2 : F) ≠ 0)
    [WeierstrassCurve.IsElliptic (AffineGroup.mathCurve curve)]
    (scalar : Nat) (point : LawfulAffine.Point F)
    (hpoint : LawfulAffine.OnCurve curve point) :
    AffineGroup.toMathlib curve
        ⟨binary .infinity (LawfulAffine.add curve)
            (LawfulAffine.double curve) scalar point,
          binary_preserves .infinity (LawfulAffine.add curve)
            (LawfulAffine.double curve) (LawfulAffine.OnCurve curve)
            (LawfulAffine.onCurve_infinity curve)
            (fun left right => LawfulAffine.onCurve_add curve left right h2)
            (fun lifted => LawfulAffine.onCurve_double curve lifted h2)
            scalar point hpoint⟩ =
      scalar • AffineGroup.toMathlib curve ⟨point, hpoint⟩ := by
  let zeroPoint : AffineGroup.Point curve := AffineGroup.infinity curve
  let addPoint : AffineGroup.Point curve → AffineGroup.Point curve →
      AffineGroup.Point curve := AffineGroup.add curve h2
  let doublePoint : AffineGroup.Point curve → AffineGroup.Point curve :=
    AffineGroup.double curve h2
  have hmap := binary_map_nsmul zeroPoint addPoint doublePoint
    (AffineGroup.toMathlib curve)
    (AffineGroup.toMathlib_infinity curve)
    (AffineGroup.toMathlib_add curve h2)
    (AffineGroup.toMathlib_double curve h2)
    scalar (⟨point, hpoint⟩ : AffineGroup.Point curve)
  have hval := binary_lift_val .infinity (LawfulAffine.add curve)
    (LawfulAffine.double curve) (LawfulAffine.OnCurve curve)
    (LawfulAffine.onCurve_infinity curve)
    (fun left right => LawfulAffine.onCurve_add curve left right h2)
    (fun lifted => LawfulAffine.onCurve_double curve lifted h2)
    scalar point hpoint
  have heq :
      binary zeroPoint addPoint doublePoint scalar
          (⟨point, hpoint⟩ : AffineGroup.Point curve) =
        ⟨binary .infinity (LawfulAffine.add curve)
            (LawfulAffine.double curve) scalar point,
          binary_preserves .infinity (LawfulAffine.add curve)
            (LawfulAffine.double curve) (LawfulAffine.OnCurve curve)
            (LawfulAffine.onCurve_infinity curve)
            (fun left right => LawfulAffine.onCurve_add curve left right h2)
            (fun lifted => LawfulAffine.onCurve_double curve lifted h2)
            scalar point hpoint⟩ := by
    apply Subtype.ext
    exact hval
  rw [heq] at hmap
  exact hmap

/-- G1 scalar multiplication agrees with the independent Mathlib affine
group's natural-number scalar action. -/
theorem g1_nsmul (scalar : Nat) (point : G1Affine.Point)
    (hpoint : G1Affine.OnCurve point) :
    AffineGroup.toMathlib G1Affine.curve
        ⟨g1 scalar point, g1_onCurve scalar point hpoint⟩ =
      scalar • AffineGroup.toMathlib G1Affine.curve ⟨point, hpoint⟩ := by
  simpa [g1, G1Affine.add, G1Affine.double] using
    binary_onCurve_nsmul G1Affine.curve G1Affine.two_ne_zero
      scalar point hpoint

/-- G2 scalar multiplication agrees with the independent Mathlib affine
group's natural-number scalar action. -/
theorem g2_nsmul (scalar : Nat) (point : G2Affine.Point)
    (hpoint : G2Affine.OnCurve point) :
    AffineGroup.toMathlib G2Affine.curve
        ⟨g2 scalar point, g2_onCurve scalar point hpoint⟩ =
      scalar • AffineGroup.toMathlib G2Affine.curve ⟨point, hpoint⟩ := by
  simpa [g2, G2Affine.add, G2Affine.double] using
    binary_onCurve_nsmul G2Affine.curve G2Affine.two_ne_zero
      scalar point hpoint

end Challenge.Bls12381.ProofSupport.ScalarMul
