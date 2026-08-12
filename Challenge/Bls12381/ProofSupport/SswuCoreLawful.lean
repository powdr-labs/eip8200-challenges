import Challenge.Bls12381.ProofSupport.SswuCore
import Mathlib.Tactic.Ring

set_option warningAsError true

/-! # Algebraic correctness of the generic simplified-SWU schedule -/

namespace Challenge.Bls12381.ProofSupport.SswuCore

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Sign selection preserves the square of the selected root. -/
theorem signAdjusted_sq (suite : Suite F) (u y : F) :
    signAdjusted suite u y ^ 2 = y ^ 2 := by
  unfold signAdjusted
  split <;> ring

private theorem denominatorFactor_ne_zero (suite : Suite F)
    (hA : suite.A ≠ 0) (hZ : suite.Z ≠ 0) (tv2 : F) :
    suite.A * (if tv2 = 0 then suite.Z else -tv2) ≠ 0 := by
  apply mul_ne_zero hA
  split
  · exact hZ
  · exact neg_ne_zero.mpr ‹tv2 ≠ 0›

/-- The source CMOV makes the denominator cube nonzero for every input. -/
theorem denominator_ne_zero (suite : Suite F)
    (hA : suite.A ≠ 0) (hZ : suite.Z ≠ 0) (u : F) :
    denominator suite u ≠ 0 := by
  unfold denominator
  dsimp only
  apply mul_ne_zero
  · exact pow_ne_zero 2 (denominatorFactor_ne_zero suite hA hZ _)
  · exact denominatorFactor_ne_zero suite hA hZ _

/-- Observable refinement for the final source sign-selection branch. -/
theorem projective_y_eq_source (suite : Suite F)
    (sqrtRatio : F → F → Bool × F) (u : F) :
    (projective suite sqrtRatio u).y =
      signAdjusted suite u (sourceY0 suite sqrtRatio u) := by
  rfl

omit [DecidableEq F] in
private theorem qr_projective (suite : Suite F) (xN xD y : F)
    (hy : y ^ 2 * (xD ^ 2 * xD) =
      (xN ^ 2 + suite.A * xD ^ 2) * xN +
        suite.B * (xD ^ 2 * xD)) :
    y ^ 2 * xD ^ 3 =
      xN ^ 3 + suite.A * xN * xD ^ 2 + suite.B * xD ^ 3 := by
  rw [show xD ^ 3 = xD ^ 2 * xD by ring]
  rw [hy]
  ring

omit [DecidableEq F] in
private theorem nonqr_projective (suite : Suite F)
    (u tv1 tv2 xN xD y : F)
    (htv1 : tv1 = suite.Z * u ^ 2)
    (htv2 : tv2 = tv1 ^ 2 + tv1)
    (hxN : xN = suite.B * (tv2 + 1))
    (hxd : xD = suite.A * -tv2)
    (hy : y ^ 2 * (xD ^ 2 * xD) = suite.Z *
      ((xN ^ 2 + suite.A * xD ^ 2) * xN +
        suite.B * (xD ^ 2 * xD))) :
    (tv1 * u * y) ^ 2 * xD ^ 3 =
      (tv1 * xN) ^ 3 + suite.A * (tv1 * xN) * xD ^ 2 +
        suite.B * xD ^ 3 := by
  rw [show xD ^ 3 = xD ^ 2 * xD by ring]
  calc
    (tv1 * u * y) ^ 2 * (xD ^ 2 * xD) =
        tv1 ^ 2 * u ^ 2 * (y ^ 2 * (xD ^ 2 * xD)) := by ring
    _ = tv1 ^ 2 * u ^ 2 *
        (suite.Z * ((xN ^ 2 + suite.A * xD ^ 2) * xN +
          suite.B * (xD ^ 2 * xD))) := by rw [hy]
    _ = (tv1 * xN) ^ 3 + suite.A * (tv1 * xN) * xD ^ 2 +
        suite.B * (xD ^ 2 * xD) := by
      rw [hxN, hxd, htv2, htv1]
      ring

/-- The exceptional `tv2 = 0` ratio is quadratic.  Concrete suites discharge
this premise with a fixed checked witness. -/
def ExceptionalRatioIsSquare (suite : Suite F) : Prop :=
  let xN := suite.B
  let xD := suite.A * suite.Z
  let numerator := (xN ^ 2 + suite.A * xD ^ 2) * xN +
    suite.B * (xD ^ 2 * xD)
  IsSquareRatio numerator (xD ^ 2 * xD)

/-- The exact generic schedule lands on its suite curve whenever the concrete
sqrt-ratio result satisfies the source contract at this input. -/
theorem projective_onCurve_of_valid (suite : Suite F)
    (hexceptional : ExceptionalRatioIsSquare suite)
    (sqrtRatio : F → F → Bool × F) (u : F)
    (hvalidAt : SqrtRatioValid suite (numerator suite u)
      (denominator suite u)
      (sqrtRatio (numerator suite u) (denominator suite u))) :
    ProjectiveOnCurve suite (projective suite sqrtRatio u) := by
  let tv1 := suite.Z * u ^ 2
  let tv2 := tv1 ^ 2 + tv1
  let tv3 := suite.B * (tv2 + 1)
  let tv4 := suite.A * if tv2 = 0 then suite.Z else -tv2
  let num := (tv3 ^ 2 + suite.A * tv4 ^ 2) * tv3 +
    suite.B * (tv4 ^ 2 * tv4)
  let den := tv4 ^ 2 * tv4
  have hvalid : SqrtRatioValid suite num den (sqrtRatio num den) := by
    simpa [numerator, denominator, tv1, tv2, tv3, tv4, num, den] using
      hvalidAt
  generalize hratio : sqrtRatio num den = ratio
  rcases ratio with ⟨isQr, root⟩
  rw [hratio] at hvalid
  change (if isQr then root ^ 2 * den = num
    else root ^ 2 * den = suite.Z * num ∧
      ¬ IsSquareRatio num den) at hvalid
  have hratio' : sqrtRatio
      ((tv3 ^ 2 + suite.A * tv4 ^ 2) * tv3 +
        suite.B * (tv4 ^ 2 * tv4))
      (tv4 ^ 2 * tv4) = (isQr, root) := by
    simpa [num, den] using hratio
  unfold ProjectiveOnCurve projective
  dsimp only
  rw [hratio']
  dsimp only
  change signAdjusted suite u
      (if isQr then root else tv1 * u * root) ^ 2 * tv4 ^ 3 =
    (if isQr then tv3 else tv1 * tv3) ^ 3 +
      suite.A * (if isQr then tv3 else tv1 * tv3) * tv4 ^ 2 +
        suite.B * tv4 ^ 3
  rw [signAdjusted_sq]
  cases isQr with
  | true =>
      simp only [if_true] at hvalid ⊢
      exact qr_projective suite tv3 tv4 root hvalid
  | false =>
      simp only [Bool.false_eq_true, if_false] at hvalid ⊢
      by_cases htv2 : tv2 = 0
      · have hratioSquare : IsSquareRatio num den := by
          simpa [ExceptionalRatioIsSquare, tv1, tv2, tv3, tv4, num, den,
            htv2] using hexceptional
        exact False.elim (hvalid.2 hratioSquare)
      · exact nonqr_projective suite u tv1 tv2 tv3 tv4 root rfl rfl rfl
          (by simp [tv4, htv2]) hvalid.1

/-- The generic schedule is total for a nonzero-parameter suite whose
sqrt-ratio dependency satisfies the source contract on nonzero denominators. -/
theorem projective_onCurve (suite : Suite F)
    (hA : suite.A ≠ 0) (hZ : suite.Z ≠ 0)
    (hexceptional : ExceptionalRatioIsSquare suite)
    (sqrtRatio : F → F → Bool × F)
    (hsqrt : ∀ u v, v ≠ 0 → SqrtRatioValid suite u v (sqrtRatio u v))
    (u : F) :
    ProjectiveOnCurve suite (projective suite sqrtRatio u) := by
  apply projective_onCurve_of_valid suite hexceptional sqrtRatio u
  apply hsqrt
  exact denominator_ne_zero suite hA hZ u

end Challenge.Bls12381.ProofSupport.SswuCore
