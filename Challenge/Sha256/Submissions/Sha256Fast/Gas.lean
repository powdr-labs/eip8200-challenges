import Challenge.Sha256.AdditionalGoals.GasSchedule
import Challenge.Sha256.Submissions.Sha256Fast.Bytecode
import Challenge.Sha256.Submissions.Sha256Fast.Proofs.EndToEndCorrect

set_option warningAsError true
set_option maxRecDepth 30000

namespace Challenge.Sha256.Submissions.Sha256Fast

open Challenge.Sha256
open EvmSemantics EvmSemantics.EVM
open Proofs Proofs.DriverLoop

/-- A simple monotone upper bound. It is exact except at the two-padding-block
boundary, where it has 31 gas of headroom. -/
def gasFormula : GasFormula :=
  1323 + 21229 * ((GasFormula.calldataSize + 72) / 64)

def gasSchedule : Nat → Nat := gasFormula.eval

private theorem paddedBlocks_short (n : Nat) (h : n % 64 < 56) :
    (n + 72) / 64 = n / 64 + 1 := by
  have hr := Nat.mod_lt n (by omega : 0 < 64)
  have hd := Nat.div_add_mod n 64
  omega

private theorem paddedBlocks_long (n : Nat) (h : ¬ n % 64 < 56) :
    (n + 72) / 64 = n / 64 + 2 := by
  have hr := Nat.mod_lt n (by omega : 0 < 64)
  have hd := Nat.div_add_mod n 64
  omega

theorem exactGas_le_gasSchedule (input : ByteArray) (hfit : CalldataFits input) :
    (EndToEndTrace.gasSteps_finalState input hfit).cost ≤
      gasSchedule input.size := by
  rw [EndToEndTrace.gasSteps_finalState_cost]
  change 22552 + blockCount input * 21229 +
      (if input.size % 64 < 56 then 0 else 21198) ≤
    1323 + 21229 * ((input.size + 72) / 64)
  by_cases hs : input.size % 64 < 56
  · rw [if_pos hs, paddedBlocks_short input.size hs]
    simp [blockCount]
    omega
  · rw [if_neg hs, paddedBlocks_long input.size hs]
    simp [blockCount]
    omega

theorem gasSchedule_correct : CorrectWithSchedule bytecode gasSchedule := by
  intro input hfit gas hgas
  let trace := EndToEndTrace.gasSteps_finalState input hfit
  have htraceGas : trace.cost ≤ gas :=
    (exactGas_le_gasSchedule input hfit).trans hgas
  have hsteps : Steps (Challenge.Sha256.initialState bytecode input gas)
      (Challenge.EvmProof.withGas (EndToEndTrace.finalState input)
        (gas - trace.cost)) := by
    change Steps
      (Challenge.EvmProof.withGas (InitializationDriver.initial input) gas)
      (Challenge.EvmProof.withGas (EndToEndTrace.finalState input)
        (gas - trace.cost))
    exact trace.trace gas htraceGas
  have heval := Challenge.EvmProof.eval_of_steps hsteps (by
    change (EndToEndTrace.finalState input).isDone = true
    exact EndToEndTrace.finalState_isDone input)
  have hresult :
      (Challenge.EvmProof.withGas (EndToEndTrace.finalState input)
        (gas - trace.cost)).toResult = .returned (Challenge.Sha256.spec input) := by
    change (EndToEndTrace.finalState input).toResult =
      .returned (Challenge.Sha256.spec input)
    exact EndToEndCorrect.finalState_toResult input hfit
  simpa [hresult] using heval

end Challenge.Sha256.Submissions.Sha256Fast
