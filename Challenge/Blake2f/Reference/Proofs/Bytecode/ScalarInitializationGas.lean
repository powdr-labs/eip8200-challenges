import Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitialization

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Exact gas certification for counter and final-flag initialization. -/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitialization

open Challenge.Blake2f
open EvmSemantics
open EvmSemantics.EVM

private theorem ofNatAdd (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.EvmProof.Word.ofNat_add_ofNat h

private def gasStepsBlock
    (path : List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    {a b : State}
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path a = some b)
    (hcode : a.executionEnv.code = referenceBytecode)
    (hfork : a.fork = .Osaka) (hrun : a.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig a.executionEnv.precompileConfig
      a.executionEnv.fork a.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps a b := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path
  · exact hcode
  · exact hfork
  · exact hresult
  · exact hrun
  · exact hnp

@[simp] private theorem gasStepsBlock_cost
    (path : List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    {a b : State}
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path a = some b)
    (hcode : a.executionEnv.code = referenceBytecode)
    (hfork : a.fork = .Osaka) (hrun : a.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig a.executionEnv.precompileConfig
      a.executionEnv.fork a.executionEnv.codeAddr = false) :
    (gasStepsBlock path hresult hcode hfork hrun hnp).cost =
      Challenge.EvmProof.Stepper.runLocatedBlockCost path a := rfl

private theorem t0SetupCost_generic (s : State) (a b : UInt256)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost t0SetupPath
      { s with pc := UInt256.ofNat 811, stack := [a, b] } = 19 := by
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlockCost,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Stepper.instrCost,
      t0SetupPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      hrun, ofNatAdd, Gas.baseCost,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem t0Setup_cost (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost t0SetupPath
      (Initialization.constantsFinalState input) = 19 := by
  simpa only [Initialization.constantsFinalState] using
    t0SetupCost_generic (Initialization.constantsFinalState input)
      (Prelude.roundsWord input) (Prelude.finalFlagWord input) rfl

private theorem t0StoreCost_generic (s : State) (x a b : UInt256)
    (hrun : s.halt = .Running) (hactive : s.activeWords = UInt256.ofNat 58) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost t0StorePath
      { s with
        pc := UInt256.ofNat 821
        stack := [x, a, b] } = 16 := by
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlockCost,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Stepper.instrCost,
      t0StorePath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      hrun, hactive, ofNatAdd, Gas.totalCost, Gas.mloadTotal, Gas.mstoreTotal,
      Gas.baseCost, MachineState.memExpansionDelta, MachineState.activeWordsAfter,
      State.activeWordsAfterUInt256, MachineState.memCost,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem t0Store_cost (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost t0StorePath
      (t0LoadedState input) = 16 := by
  simpa only [t0LoadedState, Initialization.constantsFinalState] using
    t0StoreCost_generic (Initialization.constantsFinalState input)
      (t0Word input) (Prelude.roundsWord input) (Prelude.finalFlagWord input) rfl
      rfl

private theorem t1SetupCost_generic (s : State) (a b : UInt256)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost t1SetupPath
      { s with pc := UInt256.ofNat 831, stack := [a, b] } = 19 := by
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlockCost,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Stepper.instrCost,
      t1SetupPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      hrun, ofNatAdd, Gas.baseCost,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem t1Setup_cost (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost t1SetupPath
      (t0FinalState input) = 19 := by
  simpa only [t0FinalState] using
    t1SetupCost_generic (t0FinalState input)
      (Prelude.roundsWord input) (Prelude.finalFlagWord input) rfl

private theorem t1StoreCost_generic (s : State) (x a b : UInt256)
    (hrun : s.halt = .Running) (hactive : s.activeWords = UInt256.ofNat 58) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost t1StorePath
      { s with
        pc := UInt256.ofNat 841
        stack := [x, a, b] } = 16 := by
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlockCost,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Stepper.instrCost,
      t1StorePath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      hrun, hactive, ofNatAdd, Gas.totalCost, Gas.mloadTotal, Gas.mstoreTotal,
      Gas.baseCost, MachineState.memExpansionDelta, MachineState.activeWordsAfter,
      State.activeWordsAfterUInt256, MachineState.memCost,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem t1Store_cost (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost t1StorePath
      (t1LoadedState input) = 16 := by
  simpa only [t1LoadedState] using
    t1StoreCost_generic (t0FinalState input)
      (t1Word input) (Prelude.roundsWord input) (Prelude.finalFlagWord input) rfl rfl

private theorem flagTestCost_generic (s : State) (rounds flag : UInt256)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost flagTestPath
      { s with pc := UInt256.ofNat 851, stack := [rounds, flag] } = 19 := by
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlockCost,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Stepper.instrCost,
      flagTestPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      hrun, ofNatAdd, Gas.baseCost, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem flagTestZero_cost (input : ByteArray) (_hflag : input[212]!.toNat = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost flagTestPath
      (flagEntryState input) = 19 := by
  exact flagTestCost_generic (flagEntryState input)
    (Prelude.roundsWord input) (Prelude.finalFlagWord input) rfl


theorem flagTestOne_cost (input : ByteArray) (_hflag : input[212]!.toNat = 1) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost flagTestPath
      (flagEntryState input) = 19 := by
  exact flagTestCost_generic (flagEntryState input)
    (Prelude.roundsWord input) (Prelude.finalFlagWord input) rfl

private theorem flagMutationCost_generic (s : State) (rounds flag : UInt256)
    (hrun : s.halt = .Running) (hactive : s.activeWords = UInt256.ofNat 58) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost flagMutationPath
      { s with
        pc := UInt256.ofNat 857
        stack := [rounds, flag] } = 18 := by
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlockCost,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Stepper.instrCost,
      flagMutationPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      hrun, hactive, ofNatAdd, Gas.totalCost, Gas.mloadTotal, Gas.mstoreTotal,
      Gas.baseCost, MachineState.memExpansionDelta, MachineState.activeWordsAfter,
      State.activeWordsAfterUInt256, MachineState.memCost,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem flagMutation_cost (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost flagMutationPath
      (flagMutationState input) = 18 := by
  simpa only [flagMutationState, flagEntryState] using
    flagMutationCost_generic (flagEntryState input)
      (Prelude.roundsWord input) (Prelude.finalFlagWord input) rfl rfl

private theorem flagFinishCost_generic (s : State) (rounds flag : UInt256)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost flagFinishPath
      { s with pc := UInt256.ofNat 875, stack := [rounds, flag] } = 4 := by
  simp (config := { maxSteps := 300000 })
    [Challenge.EvmProof.Stepper.runLocatedBlockCost,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Stepper.instrCost,
      flagFinishPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      hrun, Gas.baseCost,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem flagFinish_cost (input : ByteArray) (memory : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost flagFinishPath
      (flagJoinState input memory) = 4 := by
  exact flagFinishCost_generic (flagJoinState input memory)
    (Prelude.roundsWord input) (Prelude.finalFlagWord input) rfl

private theorem return821_valid :
    Decode.isValidJumpDest referenceBytecode 821 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 406 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

private theorem return841_valid :
    Decode.isValidJumpDest referenceBytecode 841 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 417 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

def t0GasSteps (input : ByteArray) :
    Challenge.EvmProof.GasSteps (Initialization.constantsFinalState input)
      (t0FinalState input) := by
  have gsetup := gasStepsBlock t0SetupPath (run_t0Setup input)
    rfl rfl rfl deployAddress_not_precompile
  have gload := LoadLE64.gasSteps (Initialization.constantsFinalState input)
    (UInt256.ofNat 196) (UInt256.ofNat 821)
    [Prelude.roundsWord input, Prelude.finalFlagWord input]
    (by simp) rfl rfl rfl deployAddress_not_precompile return821_valid
  have gstore := gasStepsBlock t0StorePath (run_t0Store input)
    rfl rfl rfl deployAddress_not_precompile
  have hoff : (UInt256.ofNat 196).toNat = 196 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by norm_num)]
  exact Challenge.EvmProof.GasSteps.cast
    (gsetup.trans ((Challenge.EvmProof.GasSteps.cast gload rfl (by
      simp [LoadLE64.finalState, t0LoadedState, t0Word,
        Initialization.decodedWord, Initialization.constantsFinalState,
        Prelude.finalState, initialState, hoff])).trans gstore)) rfl rfl

@[simp] theorem t0GasSteps_cost (input : ByteArray) :
    (t0GasSteps input).cost = 752 := by
  unfold t0GasSteps
  simp only [Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.GasSteps.trans_cost, gasStepsBlock_cost]
  rw [t0Setup_cost input]
  rw [LoadLE64.gasSteps_cost]
  rw [t0Store_cost input]

def t1GasSteps (input : ByteArray) :
    Challenge.EvmProof.GasSteps (t0FinalState input) (flagEntryState input) := by
  have gsetup := gasStepsBlock t1SetupPath (run_t1Setup input)
    rfl rfl rfl deployAddress_not_precompile
  have gload := LoadLE64.gasSteps (t0FinalState input)
    (UInt256.ofNat 204) (UInt256.ofNat 841)
    [Prelude.roundsWord input, Prelude.finalFlagWord input]
    (by simp) rfl rfl rfl deployAddress_not_precompile return841_valid
  have gstore := gasStepsBlock t1StorePath (run_t1Store input)
    rfl rfl rfl deployAddress_not_precompile
  have hoff : (UInt256.ofNat 204).toNat = 204 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by norm_num)]
  exact Challenge.EvmProof.GasSteps.cast
    (gsetup.trans ((Challenge.EvmProof.GasSteps.cast gload rfl (by
      simp [LoadLE64.finalState, t1LoadedState, t1Word,
        Initialization.decodedWord, t0FinalState,
        Initialization.constantsFinalState, Prelude.finalState, initialState,
        hoff])).trans gstore)) rfl rfl

@[simp] theorem t1GasSteps_cost (input : ByteArray) :
    (t1GasSteps input).cost = 752 := by
  unfold t1GasSteps
  simp only [Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.GasSteps.trans_cost, gasStepsBlock_cost]
  rw [t1Setup_cost input]
  rw [LoadLE64.gasSteps_cost]
  rw [t1Store_cost input]

def flagZeroGasSteps (input : ByteArray) (hflag : input[212]!.toNat = 0) :
    Challenge.EvmProof.GasSteps (flagEntryState input) (roundEntryState input) := by
  have gtest := gasStepsBlock flagTestPath (run_flagTestZero input hflag)
    rfl rfl rfl deployAddress_not_precompile
  have gfinish := gasStepsBlock flagFinishPath (run_flagFinish input (t1Memory input))
    rfl rfl rfl deployAddress_not_precompile
  exact Challenge.EvmProof.GasSteps.cast (gtest.trans gfinish) rfl (by
    simp [roundEntryState, finalMemory, hflag])

@[simp] theorem flagZeroGasSteps_cost (input : ByteArray)
    (hflag : input[212]!.toNat = 0) :
    (flagZeroGasSteps input hflag).cost = 23 := by
  unfold flagZeroGasSteps
  simp only [Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.GasSteps.trans_cost, gasStepsBlock_cost]
  rw [flagTestZero_cost input hflag, flagFinish_cost input (t1Memory input)]

def flagOneGasSteps (input : ByteArray) (hflag : input[212]!.toNat = 1) :
    Challenge.EvmProof.GasSteps (flagEntryState input) (roundEntryState input) := by
  have gtest := gasStepsBlock flagTestPath (run_flagTestOne input hflag)
    rfl rfl rfl deployAddress_not_precompile
  have gmutation := gasStepsBlock flagMutationPath (run_flagMutation input)
    rfl rfl rfl deployAddress_not_precompile
  have gfinish := gasStepsBlock flagFinishPath (run_flagFinish input (flaggedMemory input))
    rfl rfl rfl deployAddress_not_precompile
  exact Challenge.EvmProof.GasSteps.cast
    (gtest.trans (gmutation.trans gfinish)) rfl (by
      simp [roundEntryState, finalMemory, hflag])

@[simp] theorem flagOneGasSteps_cost (input : ByteArray)
    (hflag : input[212]!.toNat = 1) :
    (flagOneGasSteps input hflag).cost = 41 := by
  unfold flagOneGasSteps
  simp only [Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.GasSteps.trans_cost, gasStepsBlock_cost]
  rw [flagTestOne_cost input hflag, flagMutation_cost input,
    flagFinish_cost input (flaggedMemory input)]

def gasSteps (input : ByteArray) (hflag : input[212]!.toNat ≤ 1) :
    Challenge.EvmProof.GasSteps (Initialization.constantsFinalState input)
      (roundEntryState input) := by
  by_cases hzero : input[212]!.toNat = 0
  · exact (t0GasSteps input).trans
      ((t1GasSteps input).trans (flagZeroGasSteps input hzero))
  · have hone : input[212]!.toNat = 1 := by omega
    exact (t0GasSteps input).trans
      ((t1GasSteps input).trans (flagOneGasSteps input hone))

@[simp] theorem gasSteps_cost (input : ByteArray)
    (hflag : input[212]!.toNat ≤ 1) :
    (gasSteps input hflag).cost = 1527 + 18 * input[212]!.toNat := by
  unfold gasSteps
  split
  · simp_all
  · have hone : input[212]!.toNat = 1 := by omega
    simp_all

def fullGasSteps (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 213) (hflag : input[212]!.toNat ≤ 1) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (roundEntryState input) :=
  (Prelude.gasSteps input hfit hsize hflag).trans
    ((Initialization.hLoopGasSteps input).trans
      ((Initialization.mLoopGasSteps input).trans
        ((Initialization.vLoopGasSteps input).trans
          ((Initialization.constantsGasSteps input).trans
            (gasSteps input hflag)))))

@[simp] theorem fullGasSteps_cost (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 213) (hflag : input[212]!.toNat ≤ 1) :
    (fullGasSteps input hfit hsize hflag).cost =
      22300 + 18 * input[212]!.toNat := by
  unfold fullGasSteps
  simp only [Challenge.EvmProof.GasSteps.trans_cost]
  rw [Prelude.gasSteps_cost input hfit hsize hflag,
    Initialization.hLoopGasSteps_cost input,
    Initialization.mLoopGasSteps_cost input,
    Initialization.vLoopGasSteps_cost input,
    Initialization.constantsGasSteps_cost input,
    gasSteps_cost input hflag]
  omega

end Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitialization
