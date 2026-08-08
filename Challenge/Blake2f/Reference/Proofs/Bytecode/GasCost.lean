import Challenge.Blake2f.AdditionalGoals.GasSchedule
set_option warningAsError true

/-!
# Closed gas schedules for the frozen BLAKE2f artifact

The valid path has one constant-cost round body. Malformed lengths reach the
first `INVALID`; a malformed final flag reaches the second. `gasFormula`
uses the larger exceptional-path threshold so it is a single reusable
sufficient schedule expressible with the public symbolic language.
-/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.GasCost

open Challenge.Blake2f
open EvmSemantics.EVM

def validBase : Nat := 29213
def roundCost : Nat := 3970
def finalFlagCost : Nat := 18
def invalidLengthCost : Nat := 57
def invalidFlagCost : Nat := 94

def finalFlag (input : ByteArray) : Nat := input[212]!.toNat

/-- Exact instruction gas consumed before RETURN or INVALID. -/
def referenceGas (input : ByteArray) : Nat :=
  if input.size = 213 then
    if finalFlag input ≤ 1 then
      validBase + roundCost * rounds input + finalFlagCost * finalFlag input
    else invalidFlagCost
  else invalidLengthCost

/-- Public symbolic sufficient bound. Its invalid arm deliberately uses the
larger of the two exceptional paths. -/
def gasFormula : GasFormula :=
  .ifValid
    (.constant validBase + .constant roundCost * .rounds +
      .constant finalFlagCost * .finalFlag)
    (.constant invalidFlagCost)

def gasSchedule : ByteArray → Nat := gasFormula.eval

theorem gasSchedule_eq (input : ByteArray) :
    gasSchedule input =
      if validInput input then
        validBase + roundCost * rounds input + finalFlagCost * finalFlag input
      else invalidFlagCost := by
  rfl

theorem referenceGas_le_gasSchedule (input : ByteArray) :
    referenceGas input ≤ gasSchedule input := by
  by_cases hsize : input.size = 213
  · rw [referenceGas, if_pos hsize, gasSchedule_eq]
    have hbang : input[212]! = input[212] := getElem!_pos input 212 (by omega)
    by_cases hflag : finalFlag input ≤ 1
    · rw [if_pos hflag]
      have hbyte : input[212]!.toNat = 0 ∨ input[212]!.toNat = 1 := by
        simpa [finalFlag] using (show finalFlag input = 0 ∨ finalFlag input = 1 by omega)
      rcases hbyte with hzero | hone
      · have hvalue : input[212]! = 0 := UInt8.toNat_inj.mp (by simpa using hzero)
        rw [hbang] at hvalue
        simp [validInput, Precompile.blake2fInputLength, hsize, hvalue, finalFlag]
      · have hvalue : input[212]! = 1 := UInt8.toNat_inj.mp (by simpa using hone)
        rw [hbang] at hvalue
        simp [validInput, Precompile.blake2fInputLength, hsize, hvalue, finalFlag]
    · rw [if_neg hflag]
      have hzero : input[212]! ≠ 0 := by
        intro h
        apply hflag
        simp [finalFlag, h]
      have hone : input[212]! ≠ 1 := by
        intro h
        apply hflag
        simp [finalFlag, h]
      rw [hbang] at hzero hone
      simp [validInput, Precompile.blake2fInputLength, hsize, hzero, hone]
  · rw [referenceGas, if_neg hsize, gasSchedule_eq]
    simp [validInput, Precompile.blake2fInputLength, hsize,
      invalidLengthCost, invalidFlagCost]

end Challenge.Blake2f.Reference.Proofs.Bytecode.GasCost
