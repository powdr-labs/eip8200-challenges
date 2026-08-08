import Challenge.Blake2f.Reference.Proofs.Bytecode.Invalid
import Challenge.Blake2f.Reference.Proofs.Bytecode.OutputCorrectness
import Challenge.Blake2f.Reference.Proofs.Bytecode.OutputGas

set_option warningAsError true
set_option maxHeartbeats 1000000

/-!
# End-to-end correctness of the frozen BLAKE2f reference bytecode

This module composes the validation, initialization, round, fold, and output
traces. It proves both the challenge specification and the exact
calldata-dependent gas cost used by the public schedule.
-/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.ReferenceCorrect

open Challenge.Blake2f
open EvmSemantics
open EvmSemantics.EVM

private theorem validInput_iff (input : ByteArray) :
    validInput input = true ↔
      input.size = 213 ∧ input[212]!.toNat ≤ 1 := by
  rw [validInput, Bool.and_eq_true, Bool.or_eq_true]
  simp only [beq_iff_eq]
  constructor
  · rintro ⟨hsize, hzero | hone⟩
    · simp [Precompile.blake2fInputLength] at hsize
      refine ⟨hsize, ?_⟩
      rw [getElem!_pos input 212 (by omega)] at hzero
      rw [getElem!_pos input 212 (by omega), hzero]
      decide
    · simp [Precompile.blake2fInputLength] at hsize
      refine ⟨hsize, ?_⟩
      rw [getElem!_pos input 212 (by omega)] at hone
      rw [getElem!_pos input 212 (by omega), hone]
      decide
  · rintro ⟨hsize, hflag⟩
    have hcases : input[212]!.toNat = 0 ∨ input[212]!.toNat = 1 := by omega
    constructor
    · simpa [Precompile.blake2fInputLength] using hsize
    · rcases hcases with hzero | hone
      · left
        exact UInt8.toNat_inj.mp (by simpa using hzero)
      · right
        exact UInt8.toNat_inj.mp (by simpa using hone)

theorem roundsWord_toNat (input : ByteArray) :
    (Prelude.roundsWord input).toNat = rounds input := by
  rw [Prelude.roundsWord, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (OutputCorrectness.rounds_lt input)]

theorem schedule_memories {initial : ByteArray} (count : Nat)
    (schedule : RoundCorrectness.ScheduleRows initial) :
    RoundCorrectness.ScheduleRows (Round.memories initial count) := by
  induction count with
  | zero => simpa [Round.memories] using schedule
  | succ count ih =>
      rw [Round.memories]
      exact RoundCorrectness.schedule_transition_round count ih

def validFinalState (input : ByteArray) : State :=
  Output.finalState (Initialization.constantsFinalState input)
    (Round.memories (ScalarInitialization.finalMemory input)
      (Prelude.roundsWord input).toNat)
    (Prelude.roundsWord input) (Prelude.finalFlagWord input)

/-- The complete successful trace for a valid EIP-152 input. -/
def validGasSteps (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 213) (hflag : input[212]!.toNat ≤ 1) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (validFinalState input) := by
  let s := Initialization.constantsFinalState input
  have safe : ∀ round, round < (Prelude.roundsWord input).toNat →
      Round.IterationSafe
        (Round.memories (ScalarInitialization.finalMemory input) round) round := by
    intro round hround
    apply RoundCorrectness.iterationSafe_of_schedule
    · rw [roundsWord_toNat] at hround
      exact Nat.lt_trans hround (OutputCorrectness.rounds_lt input)
    · exact schedule_memories round
        (RoundCorrectness.schedule_finalMemory input)
  have ginit := ScalarInitialization.fullGasSteps input hfit hsize hflag
  have ground := Round.loopGasSteps s (ScalarInitialization.finalMemory input)
    (Prelude.roundsWord input) (Prelude.finalFlagWord input) safe
    (by rfl) (by rfl) (by rfl) (by exact deployAddress_not_precompile)
  have gout := Output.gasSteps s
    (Round.memories (ScalarInitialization.finalMemory input)
      (Prelude.roundsWord input).toNat)
    (Prelude.roundsWord input) (Prelude.finalFlagWord input)
    (by rfl) (by rfl) (by rfl) (by exact deployAddress_not_precompile)
  exact Challenge.EvmProof.GasSteps.cast
    (ginit.trans (ground.trans gout)) rfl rfl

@[simp] theorem validGasSteps_cost (input : ByteArray)
    (hfit : CalldataFits input) (hsize : input.size = 213)
    (hflag : input[212]!.toNat ≤ 1) :
    (validGasSteps input hfit hsize hflag).cost =
      GasCost.validBase + GasCost.roundCost * rounds input +
        GasCost.finalFlagCost * input[212]!.toNat := by
  unfold validGasSteps
  simp only [Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.GasSteps.trans_cost]
  rw [ScalarInitialization.fullGasSteps_cost, Round.loopGasSteps_cost,
    Output.gasSteps_cost, roundsWord_toNat]
  simp [GasCost.validBase, GasCost.roundCost, GasCost.finalFlagCost]
  omega

@[simp] theorem validFinalState_isDone (input : ByteArray) :
    (validFinalState input).isDone = true := by
  simp [validFinalState, Output.finalState, Output.baseState,
    Initialization.constantsFinalState, Prelude.finalState,
    State.isDone, State.isHalted, State.isRunning, initialState]

theorem validFinalState_toResult (input : ByteArray)
    (hflag : input[212]!.toNat ≤ 1) :
    (validFinalState input).toResult = .returned (spec input) := by
  rw [State.toResult_returned _ (by rfl)]
  congr 1
  unfold validFinalState
  rw [roundsWord_toNat]
  exact OutputCorrectness.finalState_return_eq_spec
    (Initialization.constantsFinalState input) input hflag

private theorem eval_of_gasSteps {initial final : State}
    (trace : Challenge.EvmProof.GasSteps initial final)
    (gas : Nat) (hgas : trace.cost ≤ gas)
    (hdone : final.isDone = true) :
    Eval (Challenge.EvmProof.withGas initial gas) final.toResult := by
  have steps := trace.trace gas hgas
  have result := Challenge.EvmProof.eval_of_steps steps (by
    change final.isDone = true
    exact hdone)
  have hresult :
      (Challenge.EvmProof.withGas final (gas - trace.cost)).toResult =
        final.toResult := by
    cases final
    rfl
  rw [hresult] at result
  exact result

private theorem withGas_initialState (code input : ByteArray) (gas : Nat) :
    Challenge.EvmProof.withGas (initialState code input 0) gas =
      initialState code input gas := by
  rfl

/-- The exact instruction cost suffices on every valid and invalid path. -/
theorem reference_correctWithExactGas :
    CorrectWithSchedule referenceBytecode GasCost.referenceGas := by
  intro input hfit gas hgas
  by_cases hsize : input.size = 213
  · by_cases hflag : input[212]!.toNat ≤ 1
    · let trace := validGasSteps input hfit hsize hflag
      have hcost : trace.cost = GasCost.referenceGas input := by
        rw [validGasSteps_cost, GasCost.referenceGas, if_pos hsize,
          if_pos (show GasCost.finalFlag input ≤ 1 from hflag)]
        rfl
      refine ⟨.returned (spec input), ?_, ?_⟩
      · have heval := eval_of_gasSteps trace gas (by omega)
          (validFinalState_isDone input)
        simpa [validFinalState_toResult input hflag, initialState,
          Challenge.EvmProof.withGas] using heval
      · rw [Matches, if_pos ((validInput_iff input).2 ⟨hsize, hflag⟩)]
    · have hbad : 1 < input[212]!.toNat := by omega
      let trace := Invalid.gasSteps_invalidFlag input hfit hsize hbad
      have hcost : trace.cost = GasCost.referenceGas input := by
        rw [Invalid.gasSteps_invalidFlag_cost, GasCost.referenceGas,
          if_pos hsize, if_neg (show ¬GasCost.finalFlag input ≤ 1 from hflag)]
      refine ⟨.exception .InvalidInstruction, ?_, ?_⟩
      · have heval := eval_of_gasSteps trace gas (by omega) (by
          simp [Invalid.invalidFlagFinal, State.isDone, State.isHalted,
            State.isRunning, initialState])
        rw [withGas_initialState] at heval
        simpa [Invalid.invalidFlagFinal, State.toResult] using heval
      · rw [Matches, if_neg]
        · exact ⟨.InvalidInstruction, rfl⟩
        · exact fun hvalid => hflag ((validInput_iff input).1 hvalid).2
  · let trace := Invalid.gasSteps_invalidLength input hfit hsize
    have hcost : trace.cost = GasCost.referenceGas input := by
      rw [Invalid.gasSteps_invalidLength_cost]
      simp [GasCost.referenceGas, hsize]
    refine ⟨.exception .InvalidInstruction, ?_, ?_⟩
    · have heval := eval_of_gasSteps trace gas (by omega) (by
        simp [Invalid.invalidLengthFinal, State.isDone, State.isHalted,
          State.isRunning, initialState])
      rw [withGas_initialState] at heval
      simpa [Invalid.invalidLengthFinal, State.toResult] using heval
    · rw [Matches, if_neg]
      · exact ⟨.InvalidInstruction, rfl⟩
      · exact fun hvalid => hsize ((validInput_iff input).1 hvalid).1

/-- The public symbolic formula is a sufficient gas schedule. -/
theorem reference_correctWithSchedule :
    CorrectWithSchedule referenceBytecode GasCost.gasSchedule := by
  intro input hfit gas hgas
  exact reference_correctWithExactGas input hfit gas
    (Nat.le_trans (GasCost.referenceGas_le_gasSchedule input) hgas)

/-- End-to-end canonical challenge theorem for the frozen reference bytes. -/
theorem reference_correct : Correct referenceBytecode :=
  correct_of_schedule reference_correctWithSchedule

end Challenge.Blake2f.Reference.Proofs.Bytecode.ReferenceCorrect
