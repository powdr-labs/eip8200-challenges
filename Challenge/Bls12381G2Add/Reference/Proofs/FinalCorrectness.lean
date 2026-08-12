import Challenge.Bls12381G2Add.AdditionalGoals
import Challenge.Bls12381G2Add.ProofSupport.YulInitial
import Challenge.Bls12381G2Add.Reference.Proofs.CompilerCorrectness
import Challenge.Bls12381G2Add.Reference.Proofs.SourceSpec
import Challenge.EvmProof.Execution

set_option warningAsError true

/-! # End-to-end correctness of the concrete G2ADD runtime -/

namespace Challenge.Bls12381G2Add.Reference.Proofs.FinalCorrectness

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Bls12381G2Add.Reference.Proofs

private def sourceRunFor (input : ByteArray) (hfit : input.size < 2 ^ 64) :=
  SourceSemantics.run_matches_spec
    (Challenge.Bls12381G2Add.ProofSupport.Yul.sourceInitialState
      referenceBytecode input)
    input rfl (hfit.trans (by norm_num)) rfl

private noncomputable def sourceFinal (input : ByteArray)
    (hfit : input.size < 2 ^ 64) : EvmState :=
  Classical.choose (sourceRunFor input hfit)

private noncomputable def sourceFinal_spec (input : ByteArray)
    (hfit : input.size < 2 ^ 64) :=
  Classical.choose_spec (sourceRunFor input hfit)

private noncomputable def compilerBound (input : ByteArray)
    (hfit : input.size < 2 ^ 64) : Nat :=
  Classical.choose (CompilerCorrectness.referenceCompiledBlock_correct
    (sourceFinal_spec input hfit).1)

private noncomputable def compilerBound_spec (input : ByteArray)
    (hfit : input.size < 2 ^ 64) :=
  Classical.choose_spec (CompilerCorrectness.referenceCompiledBlock_correct
    (sourceFinal_spec input hfit).1)

/-- The compiler's checked execution bound for this exact input. The bound
is proof-extracted from the concrete source run and compiled artifact; it is
not a claimed optimized gas formula. -/
noncomputable def gasSchedule (input : ByteArray) : Nat :=
  if hfit : input.size < 2 ^ 64 then
    compilerBound input hfit
  else 0

private theorem eval_resultOf_of_haltedMatch {s0 s' : State}
    {_yst' : EvmState} (hsteps : Steps s0 s') (hstack : s'.callStack = [])
    (hmatch : HaltedMatch _yst' s') :
    ∃ hk, _yst'.halted = some hk ∧ Eval s0 (resultOf hk) := by
  obtain ⟨hk, hyhalt, hh⟩ := hmatch
  refine ⟨hk, hyhalt, ?_⟩
  have hdone : s'.halt ≠ .Running ∧ s'.toResult = resultOf hk := by
    rcases hk with ⟨kind, payload⟩
    cases kind with
    | stop =>
        have hhalt : s'.halt = .Success := hh
        exact ⟨by rw [hhalt]; simp, by
          rw [State.toResult_success s' hhalt]; rfl⟩
    | ret =>
        obtain ⟨hhalt, hpayload⟩ := hh
        change s'.hReturn.toList = payload at hpayload
        refine ⟨by rw [hhalt]; simp, ?_⟩
        rw [State.toResult_returned s' hhalt]
        show ExecutionResult.returned s'.hReturn = .returned (mkCode payload)
        rw [← hpayload, mkCode_toList]
    | revert =>
        obtain ⟨hhalt, hpayload⟩ := hh
        change s'.hReturn.toList = payload at hpayload
        refine ⟨by rw [hhalt]; simp, ?_⟩
        rw [State.toResult_reverted s' hhalt]
        show ExecutionResult.reverted s'.hReturn = .reverted (mkCode payload)
        rw [← hpayload, mkCode_toList]
    | invalid =>
        have hhalt : s'.halt = .Exception .InvalidInstruction := hh
        exact ⟨by rw [hhalt]; simp, by
          rw [State.toResult_exception s' _ hhalt]; rfl⟩
    | invalidMemoryAccess =>
        have hhalt : s'.halt = .Exception .InvalidMemoryAccess := hh
        exact ⟨by rw [hhalt]; simp, by
          rw [State.toResult_exception s' _ hhalt]; rfl⟩
    | staticViolation =>
        have hhalt : s'.halt = .Exception .StaticModeViolation := hh
        exact ⟨by rw [hhalt]; simp, by
          rw [State.toResult_exception s' _ hhalt]; rfl⟩
    | selfdestruct =>
        obtain ⟨hhalt, _⟩ := hh
        exact ⟨by rw [hhalt]; simp, by
          rw [State.toResult_success s' hhalt]; rfl⟩
  rw [← hdone.2]
  exact Eval.iff_steps_halted.mpr ⟨s', hsteps, hdone.1, hstack, rfl⟩

/-- The exact 2,788-byte runtime evaluates according to the local EIP-correct
G2ADD specification at every gas budget above its checked compiler bound. -/
theorem reference_correctWithSchedule :
    CorrectWithSchedule referenceBytecode gasSchedule := by
  intro input hfit gas hgas
  have hsource := sourceFinal_spec input hfit
  have hcompiled := compilerBound_spec input hfit
  have hschedule : gasSchedule input = compilerBound input hfit := by
    simp only [gasSchedule, dif_pos hfit]
  have hbytes := Compilation.referenceInstructions_assemble
  have hframe : FrameOK (assemble Compilation.referenceInstructions)
      (initialState referenceBytecode input gas) := by
    rw [hbytes]
    exact Challenge.Bls12381G2Add.ProofSupport.Yul.initialState_frameOK
      Compilation.referenceBytecode_size_lt
  obtain ⟨s', hsteps, hstack, _hmatchState, hhalt⟩ :=
    hcompiled (initialState referenceBytecode input gas) hframe
      (Challenge.Bls12381G2Add.ProofSupport.Yul.sourceInitialState_matches
        referenceBytecode input gas)
      Challenge.Bls12381G2Add.ProofSupport.Yul.initialState_profile rfl rfl
      (by rw [hschedule] at hgas; exact hgas)
  rcases hhalt with hnormal | ⟨_, hhalted⟩
  · simp at hnormal
  · obtain ⟨hk, hyhalt, heval⟩ :=
      eval_resultOf_of_haltedMatch hsteps hstack hhalted
    refine ⟨resultOf hk, heval, ?_⟩
    cases hspec : Challenge.Bls12381G2Add.spec input with
    | none =>
        have hy : (sourceFinal input hfit).halted = some (.invalid, []) := by
          simpa [sourceFinal, hspec] using hsource.2
        have hkEq : hk = (.invalid, []) := Option.some.inj (hyhalt.symm.trans hy)
        subst hkEq
        unfold Challenge.Bls12381G2Add.Matches
        rw [hspec]
        exact ⟨.InvalidInstruction, rfl⟩
    | some output =>
        have hy : (sourceFinal input hfit).halted =
            some (.ret, output.toList) := by
          simpa [sourceFinal, hspec] using hsource.2
        have hkEq : hk = (.ret, output.toList) := Option.some.inj
          (hyhalt.symm.trans hy)
        subst hkEq
        simp [Challenge.Bls12381G2Add.Matches, hspec, resultOf, mkCode_toList]

/-- The concrete runtime satisfies the challenge's existential-gas contract. -/
theorem reference_correct : Correct referenceBytecode :=
  correct_of_schedule reference_correctWithSchedule

end Challenge.Bls12381G2Add.Reference.Proofs.FinalCorrectness
