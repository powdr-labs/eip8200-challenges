import Challenge.Sha256.Submissions.Sha256Fast.Bytecode
import Challenge.Sha256.Submissions.Sha256Fast.Proofs.EndToEndCorrect

set_option warningAsError true

namespace Challenge.Sha256.Submissions.Sha256Fast

open Challenge.Sha256.ProofSupport.Bytecode

@[simp] theorem withGas_initialState_zero (input : ByteArray) (gas : Nat) :
    Challenge.EvmProof.withGas
        (Challenge.Sha256.initialState bytecode input 0) gas =
      Challenge.Sha256.initialState bytecode input gas := by
  rfl

theorem directProof : DirectProof bytecode := by
  let Input := { calldata : ByteArray // CalldataFits calldata }
  have h := Challenge.EvmProof.GasSteps.toEventuallyEvaluates
    (initial := fun input : Input => Challenge.Sha256.initialState bytecode input.1 0)
    (final := fun input : Input => Proofs.EndToEndTrace.finalState input.1)
    (expected := fun input : Input => .returned (Challenge.Sha256.spec input.1))
    (fun input => by
      simpa [bytecode, Proofs.InitializationDriver.initial] using
        Proofs.EndToEndTrace.gasSteps_finalState input.1 input.2)
    (fun input => Proofs.EndToEndTrace.finalState_isDone input.1)
    (fun input => Proofs.EndToEndCorrect.finalState_toResult input.1 input.2)
  simpa [DirectProof, Input] using h

/-- End-to-end correctness of the submitted raw EVM bytecode. -/
theorem correct : Correct bytecode :=
  correct_of_directProof directProof

end Challenge.Sha256.Submissions.Sha256Fast
