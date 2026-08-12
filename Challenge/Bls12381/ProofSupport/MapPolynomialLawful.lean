import Challenge.Bls12381.ProofSupport.MapPolynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option warningAsError true

/-! # Lawful homogeneous polynomial evaluation -/

namespace Challenge.Bls12381.ProofSupport.MapPolynomial

section Semiring

variable {R : Type} [CommSemiring R]

theorem eval_add (left right : List R) (x : R) :
    eval (add left right) x = eval left x + eval right x := by
  induction left generalizing right with
  | nil => simp [add, eval]
  | cons a as ih =>
      cases right with
      | nil => simp [add, eval]
      | cons b bs => simp [add, eval, ih]; ring

theorem eval_scale (a : R) (coefficients : List R) (x : R) :
    eval (scale a coefficients) x = a * eval coefficients x := by
  induction coefficients with
  | nil => simp [scale, eval]
  | cons b bs ih => simp [scale, eval, ih]; ring

theorem eval_mul (left right : List R) (x : R) :
    eval (mul left right) x = eval left x * eval right x := by
  induction left with
  | nil => simp [mul, eval]
  | cons a as ih =>
      cases right with
      | nil => simp [mul, eval]
      | cons b bs =>
          simp only [mul, eval_add, eval_scale, eval, ih]
          ring

theorem eval_pow (coefficients : List R) (exponent : Nat) (x : R) :
    eval (pow coefficients exponent) x = eval coefficients x ^ exponent := by
  induction exponent with
  | zero => simp [pow, eval]
  | succ exponent ih =>
      rw [pow, eval_mul, ih, pow_succ]
      exact mul_comm _ _

end Semiring

section Field

variable {R : Type} [Field R]

/-- Homogeneous evaluation agrees with ordinary evaluation at `N / D`,
scaled by the expected denominator power. -/
theorem evalHom_eq_scaled_eval (coefficients : List R)
    (numerator denominator : R) (hcoefficients : coefficients ≠ [])
    (hdenominator : denominator ≠ 0) :
    evalHom coefficients numerator denominator =
      denominator ^ (coefficients.length - 1) *
        eval coefficients (numerator / denominator) := by
  induction coefficients with
  | nil => exact (hcoefficients rfl).elim
  | cons coefficient coefficients ih =>
      cases coefficients with
      | nil => simp [evalHom, eval]
      | cons next rest =>
          generalize hx : numerator / denominator = x at ih ⊢
          rw [evalHom]
          rw [ih (by simp)]
          simp only [List.length_cons, Nat.add_sub_cancel, eval]
          have hnumerator : denominator * x = numerator := by
            rw [← hx]
            field_simp
          rw [← hnumerator, pow_succ]
          ring

end Field

end Challenge.Bls12381.ProofSupport.MapPolynomial
