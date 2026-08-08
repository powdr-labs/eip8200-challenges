import Challenge.Blake2f.Reference.Proofs.Bytecode.ReferenceCorrect

set_option warningAsError true

/-!
# Proved gas schedule for the bundled BLAKE2f reference

The schedule depends on the encoded round count and final-block flag, because
those calldata fields determine the reference bytecode's control flow.
-/

namespace Challenge.Blake2f.Reference.Proofs.Gas

open Challenge.Blake2f
open Challenge.Blake2f.Reference.Proofs.Bytecode

/-- Symbolic formula consumed by the scorer and leaderboard. -/
def gasFormula : GasFormula := GasCost.gasFormula

/-- Evaluation of the displayed symbolic schedule. -/
def gasSchedule : ByteArray → Nat := gasFormula.eval

@[simp] theorem gasSchedule_eq (input : ByteArray) :
    gasSchedule input = GasCost.gasSchedule input := by
  rfl

/-- The displayed schedule suffices for every realizable calldata value. -/
theorem gasSchedule_correct :
    CorrectWithSchedule referenceBytecode gasSchedule := by
  intro input hfit gas hgas
  exact Bytecode.ReferenceCorrect.reference_correctWithSchedule
    input hfit gas (by simpa using hgas)

end Challenge.Blake2f.Reference.Proofs.Gas
