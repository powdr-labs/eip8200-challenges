import Challenge.Bls12381G1Add.Spec

set_option warningAsError true

namespace Challenge.Bls12381G1Add

open EvmSemantics.EVM

def CorrectWithSchedule (code : ByteArray) (schedule : ByteArray → Nat) : Prop :=
  ∀ calldata : ByteArray, calldata.size < 2 ^ 64 → ∀ gas,
    schedule calldata ≤ gas →
      ∃ result, Eval (initialState code calldata gas) result ∧ Matches calldata result

theorem correct_of_schedule {code : ByteArray} {schedule : ByteArray → Nat}
    (h : CorrectWithSchedule code schedule) : Correct code := by
  intro calldata hfit
  exact ⟨schedule calldata, fun gas hgas => h calldata hfit gas hgas⟩

end Challenge.Bls12381G1Add
