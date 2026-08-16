import EvmSemantics.EVM.BigStep
import Mathlib.Order.Monotone.Basic

set_option warningAsError true

/-!
# Machine-readable symbolic gas schedules

This module is independent of any challenge specification. Challenges use the
same small expression language to state, execute, order, and render proved gas
bounds while keeping their `CorrectWithSchedule` predicates challenge-local.
-/

namespace Challenge.EvmProof

/-- A small, executable language for monotone gas bounds. -/
inductive GasFormula where
  | calldataSize
  | constant (value : Nat)
  | add (left right : GasFormula)
  | mul (left right : GasFormula)
  | div (numerator : GasFormula) (denominator : Nat)
  | memoryCost (activeWords : GasFormula)

namespace GasFormula

/-- Interpret a symbolic gas formula at an input length. -/
def eval : GasFormula → Nat → Nat
  | .calldataSize, size => size
  | .constant value, _ => value
  | .add left right, n => left.eval n + right.eval n
  | .mul left right, n => left.eval n * right.eval n
  | .div numerator denominator, n => numerator.eval n / denominator
  | .memoryCost activeWords, n =>
      EvmSemantics.MachineState.memCost (activeWords.eval n)

/-- Every expressible schedule is monotone in the input size. -/
theorem eval_monotone (formula : GasFormula) : Monotone formula.eval := by
  induction formula with
  | calldataSize =>
      intro left right hle
      exact hle
  | constant value =>
      intro left right hle
      exact le_rfl
  | add left right leftIH rightIH =>
      intro a b hab
      exact Nat.add_le_add (leftIH hab) (rightIH hab)
  | mul left right leftIH rightIH =>
      intro a b hab
      exact Nat.mul_le_mul (leftIH hab) (rightIH hab)
  | div numerator denominator numeratorIH =>
      intro a b hab
      exact Nat.div_le_div_right (numeratorIH hab)
  | memoryCost activeWords activeWordsIH =>
      intro a b hab
      have hwords := activeWordsIH hab
      simp only [eval, EvmSemantics.MachineState.memCost]
      exact Nat.add_le_add (Nat.mul_le_mul_left 3 hwords)
        (Nat.div_le_div_right (Nat.pow_le_pow_left hwords 2))

instance (value : Nat) : OfNat GasFormula value where
  ofNat := .constant value

instance : Add GasFormula := ⟨.add⟩
instance : Mul GasFormula := ⟨.mul⟩
instance : HDiv GasFormula Nat GasFormula := ⟨.div⟩

private def parenthesize (needed : Bool) (body : String) : String :=
  if needed then "\\left(" ++ body ++ "\\right)" else body

/-- Render a formula as inline-compatible LaTeX. Division is natural-number
division, so it is shown with an explicit floor. -/
private def render : GasFormula → Nat → String
  | .calldataSize, _ => "\\mathrm{CALLDATASIZE}"
  | .constant value, _ => toString value
  | .add left right, outerPrecedence =>
      parenthesize (outerPrecedence > 1)
        (left.render 1 ++ " + " ++ right.render 1)
  | .mul left right, outerPrecedence =>
      parenthesize (outerPrecedence > 2)
        (left.render 2 ++ " \\cdot " ++ right.render 2)
  | .div numerator denominator, _ =>
      "\\left\\lfloor\\frac{" ++ numerator.render 0 ++ "}{" ++
        toString denominator ++ "}\\right\\rfloor"
  | .memoryCost activeWords, _ =>
      "C_{\\mathrm{mem}}\\left(" ++ activeWords.render 0 ++ "\\right)"

/-- LaTeX used directly by generated gas leaderboards. -/
def toLatex (formula : GasFormula) : String := formula.render 0

end GasFormula

end Challenge.EvmProof
