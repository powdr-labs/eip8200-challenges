import Challenge.EvmProof
import Challenge.Blake2f.Spec
set_option warningAsError true

namespace Challenge.Blake2f.ProofSupport.Bytecode

open EvmSemantics.EVM

/-- Submission-independent direct small-step obligation for arbitrary BLAKE2f
bytecode. It covers successful and malformed inputs in one interface. -/
def DirectProof (code : ByteArray) : Prop :=
  ∀ input : { calldata : ByteArray // CalldataFits calldata },
    ∃ cost : Nat, ∀ gas, cost ≤ gas →
      ∃ result, Eval (initialState code input.1 gas) result ∧
        Matches input.1 result

/-- A direct proof discharges the public challenge predicate. -/
theorem correct_of_directProof {code : ByteArray} (h : DirectProof code) :
    Correct code := by
  intro calldata hfit
  simpa [DirectProof] using h ⟨calldata, hfit⟩

end Challenge.Blake2f.ProofSupport.Bytecode
