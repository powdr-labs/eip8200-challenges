import Challenge.Blake2f.Spec

set_option warningAsError true

/-!
# Calldata-dependent BLAKE2f gas schedules

BLAKE2f execution depends on the four-byte round-count field, not merely on
`CALLDATASIZE`. The symbolic language therefore exposes both values and an
input-validity conditional.
-/

namespace Challenge.Blake2f

open EvmSemantics.EVM

inductive GasFormula where
  | calldataSize
  | rounds
  | finalFlag
  | constant (value : Nat)
  | add (left right : GasFormula)
  | mul (left right : GasFormula)
  | ifValid (whenValid whenInvalid : GasFormula)

namespace GasFormula

def eval : GasFormula → ByteArray → Nat
  | .calldataSize, input => input.size
  | .rounds, input => Challenge.Blake2f.rounds input
  | .finalFlag, input => input[212]!.toNat
  | .constant value, _ => value
  | .add left right, input => left.eval input + right.eval input
  | .mul left right, input => left.eval input * right.eval input
  | .ifValid whenValid whenInvalid, input =>
      if validInput input then whenValid.eval input else whenInvalid.eval input

instance (value : Nat) : OfNat GasFormula value where
  ofNat := .constant value

instance : Add GasFormula := ⟨.add⟩
instance : Mul GasFormula := ⟨.mul⟩

private def parenthesize (needed : Bool) (body : String) : String :=
  if needed then "\\left(" ++ body ++ "\\right)" else body

private def render : GasFormula → Nat → String
  | .calldataSize, _ => "\\mathrm{CALLDATASIZE}"
  | .rounds, _ => "R"
  | .finalFlag, _ => "f"
  | .constant value, _ => toString value
  | .add left right, precedence =>
      parenthesize (precedence > 1) (left.render 1 ++ " + " ++ right.render 1)
  | .mul left right, precedence =>
      parenthesize (precedence > 2) (left.render 2 ++ " \\cdot " ++ right.render 2)
  | .ifValid whenValid whenInvalid, _ =>
      "\\begin{cases}" ++ whenValid.render 0 ++ ",&\\mathrm{valid}\\\\" ++
        whenInvalid.render 0 ++ ",&\\mathrm{invalid}\\end{cases}"

def toLatex (formula : GasFormula) : String := formula.render 0

end GasFormula

/-- `schedule input` gas suffices for the complete successful-or-exceptional
behavior required by `Correct`. -/
def CorrectWithSchedule (code : ByteArray) (schedule : ByteArray → Nat) : Prop :=
  ∀ calldata : ByteArray, CalldataFits calldata → ∀ gas,
    schedule calldata ≤ gas →
      ∃ result, Eval (initialState code calldata gas) result ∧ Matches calldata result

theorem correct_of_schedule {code : ByteArray} {schedule : ByteArray → Nat}
    (h : CorrectWithSchedule code schedule) : Correct code := by
  intro calldata hfit
  exact ⟨schedule calldata, fun gas hgas => h calldata hfit gas hgas⟩

end Challenge.Blake2f
