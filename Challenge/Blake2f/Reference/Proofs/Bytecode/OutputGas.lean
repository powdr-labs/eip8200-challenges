import Challenge.Blake2f.Reference.Proofs.Bytecode.Output

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-! Exact gas composition for the post-round fold and output loop. -/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.Output

open Challenge.Blake2f
open EvmSemantics
open EvmSemantics.EVM

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

private theorem locatedCost_eq
    (path : List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    {a b : State} (work : Nat)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path a = some b)
    (hfork : a.fork = .Osaka) (hactive : b.activeWords = a.activeWords)
    (hfree : ∀ located ∈ path,
      Challenge.EvmProof.Meter.CopyFree located.instruction)
    (hwork : Challenge.EvmProof.Meter.runLocatedBlockStaticCost path = work) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path a = work := by
  have hpotential := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    path work hresult hfork hfree hwork
  rw [hactive] at hpotential
  omega

private theorem copyFree_of_all
    (path : List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    (hall : path.all
      (fun item => Challenge.EvmProof.Meter.CopyFree item.instruction) = true) :
    ∀ located ∈ path, Challenge.EvmProof.Meter.CopyFree located.instruction :=
  List.all_eq_true.mp hall

private theorem valid1149 : Decode.isValidJumpDest referenceBytecode 1149 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 574 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

theorem roundExit_cost (s : State) (memory : ByteArray) (rounds flag : UInt256)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost roundExitPath
      (Round.loopState s rounds.toNat rounds flag memory) = 25 := by
  apply locatedCost_eq roundExitPath 25
    (run_roundExit s memory rounds flag hrun hcode)
    (by simpa [Round.loopState, Round.baseState, State.fork] using hfork) rfl
  · exact copyFree_of_all roundExitPath (by decide)
  · decide

theorem init_cost (s : State) (memory : ByteArray) (rounds flag : UInt256)
    (hrun : s.halt = .Running) (hfork : s.fork = .Osaka) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost initPath
      { Round.loopState s rounds.toNat rounds flag memory with
        pc := UInt256.ofNat 1095 } = 5 := by
  apply locatedCost_eq initPath 5 (run_init s memory rounds flag hrun)
    (by simpa [Round.loopState, Round.baseState, State.fork] using hfork) rfl
  · exact copyFree_of_all initPath (by decide)
  · decide

theorem test_continue_cost (s : State) (initial : ByteArray)
    (rounds flag : UInt256) (i : Nat) (hi : i < 8)
    (hrun : s.halt = .Running) (hfork : s.fork = .Osaka) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost testPath
      (loopState s initial rounds flag i) = 26 := by
  apply locatedCost_eq testPath 26
    (run_test_continue s initial rounds flag i hi hrun)
    (by simpa [loopState, baseState, State.fork] using hfork) rfl
  · exact copyFree_of_all testPath (by decide)
  · decide

theorem test_exit_cost (s : State) (initial : ByteArray)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode) (hfork : s.fork = .Osaka) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost testPath
      (loopState s initial rounds flag 8) = 26 := by
  apply locatedCost_eq testPath 26
    (run_test_exit s initial rounds flag hrun hcode)
    (by simpa [loopState, baseState, State.fork] using hfork) rfl
  · exact copyFree_of_all testPath (by decide)
  · decide

theorem setup_cost (s : State) (initial : ByteArray) (rounds flag : UInt256)
    (i : Nat) (hi : i < 8) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode) (hfork : s.fork = .Osaka) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost setupPath
      { loopState s initial rounds flag i with pc := UInt256.ofNat 1108 } = 86 := by
  apply locatedCost_eq setupPath 86
    (run_setup s initial rounds flag i hi hrun hcode)
    (by simpa [loopState, baseState, State.fork] using hfork) rfl
  · exact copyFree_of_all setupPath (by decide)
  · decide

theorem increment_cost (s : State) (initial : ByteArray)
    (rounds flag : UInt256) (i : Nat) (hi : i < 8)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost incrementPath
      (returnedState s initial rounds flag i) = 28 := by
  apply locatedCost_eq incrementPath 28
    (run_increment s initial rounds flag i hi hrun hcode)
    (by simpa [returnedState, StoreLE64.finalState, baseState, State.fork]
      using hfork) rfl
  · exact copyFree_of_all incrementPath (by decide)
  · decide

theorem finish_cost (s : State) (initial : ByteArray) (rounds flag : UInt256)
    (hrun : s.halt = .Running) (hfork : s.fork = .Osaka) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost finishPath
      { loopState s initial rounds flag 8 with pc := UInt256.ofNat 1161 } = 9 := by
  apply locatedCost_eq finishPath 9 (run_finish s initial rounds flag hrun)
    (by simpa [loopState, baseState, State.fork] using hfork) rfl
  · exact copyFree_of_all finishPath (by decide)
  · decide

private def iterationGasSteps (s : State) (initial : ByteArray)
    (rounds flag : UInt256) (i : Nat) (hi : i < 8)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopState s initial rounds flag i)
      (loopState s initial rounds flag (i + 1)) := by
  have gtest := gasStepsBlock testPath
    (run_test_continue s initial rounds flag i hi hrun)
    (by simpa [loopState, baseState] using hcode)
    (by simpa [loopState, baseState, State.fork] using hfork)
    (by simpa [loopState, baseState] using hrun)
    (by simpa [loopState, baseState] using hnp)
  have gsetup := gasStepsBlock setupPath
    (run_setup s initial rounds flag i hi hrun hcode)
    (by simpa [loopState, baseState] using hcode)
    (by simpa [loopState, baseState, State.fork] using hfork)
    (by simpa [loopState, baseState] using hrun)
    (by simpa [loopState, baseState] using hnp)
  have gstore := StoreLE64.gasSteps
    (baseState s (outputMemory initial i))
    (UInt256.ofNat (1280 + 8 * i)) (outputWord (outputMemory initial i) i)
    (UInt256.ofNat 1149)
    [outputWord (outputMemory initial i) i, UInt256.ofNat i, rounds, flag]
    (by simp) (by simpa [baseState] using hcode)
    (by simpa [baseState, State.fork] using hfork)
    (by simpa [baseState] using hrun) (by simpa [baseState] using hnp)
    (by
      simp [baseState, Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
      omega)
    (by
      simp [baseState, Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
      omega)
    (by rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]; exact valid1149)
  have gincrement := gasStepsBlock incrementPath
    (run_increment s initial rounds flag i hi hrun hcode)
    (by simpa [returnedState, StoreLE64.finalState, baseState] using hcode)
    (by simpa [returnedState, StoreLE64.finalState, baseState, State.fork]
      using hfork)
    (by simpa [returnedState, StoreLE64.finalState, baseState] using hrun)
    (by simpa [returnedState, StoreLE64.finalState, baseState] using hnp)
  exact Challenge.EvmProof.GasSteps.cast
    (gtest.trans (gsetup.trans (gstore.trans gincrement))) rfl rfl

@[simp] private theorem iterationGasSteps_cost (s : State) (initial : ByteArray)
    (rounds flag : UInt256) (i : Nat) (hi : i < 8)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (iterationGasSteps s initial rounds flag i hi hcode hfork hrun hnp).cost = 856 := by
  unfold iterationGasSteps
  simp only [Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.GasSteps.trans_cost, gasStepsBlock_cost]
  rw [test_continue_cost s initial rounds flag i hi hrun hfork,
    setup_cost s initial rounds flag i hi hrun hcode hfork,
    StoreLE64.gasSteps_cost, increment_cost s initial rounds flag i hi hrun hcode hfork]

def gasSteps (s : State) (memory : ByteArray) (rounds flag : UInt256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (Round.loopState s rounds.toNat rounds flag memory)
      (finalState s memory rounds flag) := by
  have gexit := gasStepsBlock roundExitPath
    (run_roundExit s memory rounds flag hrun hcode)
    (by simpa [Round.loopState, Round.baseState] using hcode)
    (by simpa [Round.loopState, Round.baseState, State.fork] using hfork)
    (by simpa [Round.loopState, Round.baseState] using hrun)
    (by simpa [Round.loopState, Round.baseState] using hnp)
  have ginit := gasStepsBlock initPath (run_init s memory rounds flag hrun)
    (by simpa [Round.loopState, Round.baseState] using hcode)
    (by simpa [Round.loopState, Round.baseState, State.fork] using hfork)
    (by simpa [Round.loopState, Round.baseState] using hrun)
    (by simpa [Round.loopState, Round.baseState] using hnp)
  have gloop : Challenge.EvmProof.GasSteps
      (loopState s memory rounds flag 0) (loopState s memory rounds flag 8) :=
    Challenge.EvmProof.GasSteps.iterateBounded (count := 8)
      (I := loopState s memory rounds flag)
      (fun i hi => iterationGasSteps s memory rounds flag i hi
        hcode hfork hrun hnp)
  have gtest := gasStepsBlock testPath
    (run_test_exit s memory rounds flag hrun hcode)
    (by simpa [loopState, baseState] using hcode)
    (by simpa [loopState, baseState, State.fork] using hfork)
    (by simpa [loopState, baseState] using hrun)
    (by simpa [loopState, baseState] using hnp)
  have gfinish := gasStepsBlock finishPath (run_finish s memory rounds flag hrun)
    (by simpa [loopState, baseState] using hcode)
    (by simpa [loopState, baseState, State.fork] using hfork)
    (by simpa [loopState, baseState] using hrun)
    (by simpa [loopState, baseState] using hnp)
  exact Challenge.EvmProof.GasSteps.cast
    (gexit.trans (ginit.trans (gloop.trans (gtest.trans gfinish)))) rfl rfl

@[simp] theorem gasSteps_cost (s : State) (memory : ByteArray)
    (rounds flag : UInt256) (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (gasSteps s memory rounds flag hcode hfork hrun hnp).cost = 6913 := by
  unfold gasSteps
  simp only [Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.GasSteps.trans_cost, gasStepsBlock_cost]
  rw [roundExit_cost s memory rounds flag hrun hcode hfork,
    init_cost s memory rounds flag hrun hfork,
    test_exit_cost s memory rounds flag hrun hcode hfork,
    finish_cost s memory rounds flag hrun hfork]
  have hloop := Challenge.EvmProof.GasSteps.iterateBounded_cost_of_const
    8 856
    (fun i hi => iterationGasSteps s memory rounds flag i hi hcode hfork hrun hnp)
    (fun i hi => iterationGasSteps_cost s memory rounds flag i hi
      hcode hfork hrun hnp)
  rw [hloop]

end Challenge.Blake2f.Reference.Proofs.Bytecode.Output
