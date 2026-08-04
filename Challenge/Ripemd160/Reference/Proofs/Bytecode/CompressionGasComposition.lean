import Challenge.Ripemd160.Reference.Proofs.Bytecode.Compression80GasTrace
import Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionRunTrace

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionGasIntegration

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM
open CompressionTrace
open CompressionRightTrace
open CompressionCostTrace
open CompressionRoundCostTrace

private theorem potential_trans
    (cost₁ work₁ cost₂ work₂ p₀ p₁ p₂ : Nat)
    (h₁ : cost₁ + p₀ = work₁ + p₁)
    (h₂ : cost₂ + p₁ = work₂ + p₂) :
    (cost₁ + cost₂) + p₀ = (work₁ + work₂) + p₂ := by
  omega

private theorem rightTestExit_cost (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_rightTest_exit s messageOffset returnDest rest hstack hcode
      hfork hrun hnp).cost = Stepper.runLocatedBlockCost rightTestLocated
        (rightLoopAt s messageOffset returnDest rest 80) := by
  simp only [gasSteps_rightTest_exit, Stepper.runLocatedBlock_sound_cost]

private theorem rightExit_cost (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1021)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_rightExit s messageOffset returnDest rest hstack hcode hfork
      hrun hnp).cost = Stepper.runLocatedBlockCost rightExitLocated
        (rightExitTested s messageOffset returnDest rest) := by
  simp only [gasSteps_rightExit, Stepper.runLocatedBlock_sound_cost]

private theorem leftTestExit_cost (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_leftTest_exit s messageOffset returnDest rest hstack hcode
      hfork hrun hnp).cost = Stepper.runLocatedBlockCost leftTestLocated
        (leftLoopAt s messageOffset returnDest rest 80) := by
  simp only [gasSteps_leftTest_exit, Stepper.runLocatedBlock_sound_cost]

private theorem leftExit_cost (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1021)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_leftExit s messageOffset returnDest rest hstack hcode hfork
      hrun hnp).cost = Stepper.runLocatedBlockCost leftExitLocated
        (leftExitCompared s messageOffset returnDest rest) := by
  simp only [gasSteps_leftExit, Stepper.runLocatedBlock_sound_cost]

private theorem rightInit_cost (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1021)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (CompressionTrace.gasSteps_rightInit s messageOffset returnDest rest hstack
      hcode hfork hrun hnp).cost =
      Stepper.runLocatedBlockCost rightInitLocated
        (leftExited s messageOffset returnDest rest) := by
  simp only [CompressionTrace.gasSteps_rightInit,
    Stepper.runLocatedBlock_sound_cost]

def rightLoopAndTailWork : Nat := rightLoopWork +
  Meter.runLocatedBlockStaticCost rightTestLocated +
  Meter.runLocatedBlockStaticCost rightExitLocated + tailWork

theorem rightLoopAndTail_cost_potential (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (CompressionTailTrace.gasSteps_rightLoopAndTail s messageOffset returnDest
      rest hstack hcode hfork hrun hnp hvalid).cost +
        MachineState.memCost s.activeWords.toNat =
      rightLoopAndTailWork + MachineState.memCost
        (CompressionTailTrace.rightTailResult s messageOffset returnDest rest).activeWords.toNat := by
  let q := rightStates s messageOffset returnDest rest 80
  have hqcode : q.executionEnv.code = referenceBytecode := by
    rw [rightStates_executionEnv]
    exact hcode
  have hqfork : q.fork = .Osaka := by
    rw [State.fork, rightStates_executionEnv]
    exact hfork
  have hqrun : q.halt = .Running := by rw [rightStates_halt]; exact hrun
  have hqnp : Precompile.isPrecompile q.executionEnv.fork
      q.executionEnv.codeAddr = false := by
    simpa [q, rightStates_executionEnv] using hnp
  have h0 := right80_cost_potential s messageOffset returnDest rest hstack
    hcode hfork hrun hnp
  change (gasSteps_right80Concrete s messageOffset returnDest rest hstack
      hcode hfork hrun hnp).cost +
    MachineState.memCost s.activeWords.toNat = rightLoopWork +
      MachineState.memCost q.activeWords.toNat at h0
  have h1 := blockCost_potential rightTestLocated
    (rightLoopAt q messageOffset returnDest rest 80)
    (rightExitTested q messageOffset returnDest rest)
    (run_rightTest_exit q messageOffset returnDest rest (by omega) hqcode hqrun)
    (by simpa [rightLoopAt] using hqfork)
    (by simp [rightTestLocated, CopyFree])
  have h2 := blockCost_potential rightExitLocated
    (rightExitTested q messageOffset returnDest rest)
    (combinationEntry q messageOffset returnDest rest)
    (run_rightExit q messageOffset returnDest rest (by omega) hqrun)
    (by simpa [rightExitTested] using hqfork)
    (by simp [rightExitLocated, CopyFree])
  have h2q : Stepper.runLocatedBlockCost rightExitLocated
        (rightExitTested q messageOffset returnDest rest) +
      MachineState.memCost
        (rightExitTested q messageOffset returnDest rest).activeWords.toNat =
      Meter.runLocatedBlockStaticCost rightExitLocated +
        MachineState.memCost q.activeWords.toNat := by
    simpa [combinationEntry] using h2
  have h3 := combination_cost_potential q messageOffset returnDest rest hstack
    hqcode hqfork hqrun hqnp hvalid
  have ht : (gasSteps_rightTest_exit q messageOffset returnDest rest
        (by omega) hqcode hqfork hqrun hqnp).cost +
      MachineState.memCost q.activeWords.toNat =
      Meter.runLocatedBlockStaticCost rightTestLocated +
        MachineState.memCost
          (rightExitTested q messageOffset returnDest rest).activeWords.toNat := by
    rw [rightTestExit_cost]
    exact h1
  have he : (gasSteps_rightExit q messageOffset returnDest rest
        (by omega) hqcode hqfork hqrun hqnp).cost + MachineState.memCost
        (rightExitTested q messageOffset returnDest rest).activeWords.toNat =
      Meter.runLocatedBlockStaticCost rightExitLocated +
        MachineState.memCost q.activeWords.toNat := by
    rw [rightExit_cost]
    exact h2q
  have hc : (CompressionTailTrace.gasSteps_combination q messageOffset
        returnDest rest hstack hqcode hqfork hqrun hqnp hvalid).cost +
      MachineState.memCost q.activeWords.toNat =
      tailWork + MachineState.memCost
        (CompressionTailTrace.combinationReturned q messageOffset returnDest
          rest).activeWords.toNat := by
    exact h3
  have hshape :
      (CompressionTailTrace.gasSteps_rightLoopAndTail s messageOffset
        returnDest rest hstack hcode hfork hrun hnp hvalid).cost =
      (gasSteps_right80Concrete s messageOffset returnDest rest hstack hcode
        hfork hrun hnp).cost +
      ((gasSteps_rightTest_exit q messageOffset returnDest rest
        (by omega) hqcode hqfork hqrun hqnp).cost +
      ((gasSteps_rightExit q messageOffset returnDest rest
        (by omega) hqcode hqfork hqrun hqnp).cost +
      (CompressionTailTrace.gasSteps_combination q messageOffset returnDest
        rest hstack hqcode hqfork hqrun hqnp hvalid).cost)) := by
    rfl
  rw [hshape]
  change _ = rightLoopAndTailWork + MachineState.memCost
    (CompressionTailTrace.combinationReturned q messageOffset returnDest
      rest).activeWords.toNat
  unfold rightLoopAndTailWork
  omega

def compressToRightWork : Nat := scheduleSetupWork + scheduleWork +
  copyStateWork + Meter.runLocatedBlockStaticCost leftInitLocated +
  leftLoopWork + Meter.runLocatedBlockStaticCost leftTestLocated +
  Meter.runLocatedBlockStaticCost leftExitLocated +
  Meter.runLocatedBlockStaticCost rightInitLocated

theorem compressToRight_cost_potential (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_compressToRight s messageOffset returnDest rest hstack hcode
      hfork hrun hnp).cost + MachineState.memCost s.activeWords.toNat =
      compressToRightWork + MachineState.memCost
        (leftFinalState s messageOffset returnDest rest).activeWords.toNat := by
  let tail := messageOffset :: returnDest :: rest
  let scheduled := scheduledState s messageOffset returnDest rest
  have hsCode : scheduled.executionEnv.code = referenceBytecode := by
    simpa [scheduled, scheduledState] using hcode
  have hsFork : scheduled.fork = .Osaka := by
    simpa [scheduled, scheduledState, State.fork] using hfork
  have hsRun : scheduled.halt = .Running := by
    simpa [scheduled, scheduledState] using hrun
  have hsNp : Precompile.isPrecompile scheduled.executionEnv.fork
      scheduled.executionEnv.codeAddr = false := by
    simpa [scheduled, scheduledState] using hnp
  let initial := leftInitialState s messageOffset returnDest rest
  have hiCode : initial.executionEnv.code = referenceBytecode := by
    simpa [initial, scheduled, leftInitialState, copiedWorkingState,
      copyRegion] using hsCode
  have hiFork : initial.fork = .Osaka := by
    simpa [initial, scheduled, leftInitialState, copiedWorkingState,
      copyRegion, State.fork] using hsFork
  have hiRun : initial.halt = .Running := by
    simpa [initial, scheduled, leftInitialState, copiedWorkingState,
      copyRegion] using hsRun
  have hiNp : Precompile.isPrecompile initial.executionEnv.fork
      initial.executionEnv.codeAddr = false := by
    simpa [initial, scheduled, leftInitialState, copiedWorkingState,
      copyRegion] using hsNp
  let final := leftFinalState s messageOffset returnDest rest
  have hfCode : final.executionEnv.code = referenceBytecode := by
    simpa [final, leftFinalState, initial, leftStates_executionEnv] using hiCode
  have hfFork : final.fork = .Osaka := by
    simpa [final, initial, leftFinalState, State.fork] using hiFork
  have hfRun : final.halt = .Running := by
    simpa [final, leftFinalState, initial, leftStates_halt] using hiRun
  have hfNp : Precompile.isPrecompile final.executionEnv.fork
      final.executionEnv.codeAddr = false := by
    simpa [final, leftFinalState, initial, leftStates_executionEnv] using hiNp
  have h0 := scheduleSetup_cost_potential s messageOffset returnDest rest
    (by omega) hcode hfork hrun hnp
  have h1 := schedule_cost_potential s messageOffset (UInt256.ofNat 630) tail
    (by simp [tail]; omega) hcode hfork hrun hnp (by decide)
  have h2 := copyState_cost_potential scheduled messageOffset returnDest rest
    (by omega) hsCode hsFork hsRun hsNp
  have h3 := blockCost_potential leftInitLocated
    (copiesReturned scheduled messageOffset returnDest rest)
    (leftLoopAt initial messageOffset returnDest rest 0)
    (by simpa [initial, scheduled, leftInitialState] using
      run_leftInit scheduled messageOffset returnDest rest (by omega) hsRun)
    (by simpa [copiesReturned, copiedWorkingState, copyRegion, State.fork]
      using hsFork)
    (by simp [leftInitLocated, CopyFree])
  have h4 := left80_cost_potential initial messageOffset returnDest rest hstack
    hiCode hiFork hiRun hiNp
  have h5 := blockCost_potential leftTestLocated
    (leftLoopAt final messageOffset returnDest rest 80)
    (leftExitCompared final messageOffset returnDest rest)
    (run_leftTest_exit final messageOffset returnDest rest (by omega) hfCode hfRun)
    (by simpa [leftLoopAt] using hfFork)
    (by simp [leftTestLocated, CopyFree])
  have h6 := blockCost_potential leftExitLocated
    (leftExitCompared final messageOffset returnDest rest)
    (leftExited final messageOffset returnDest rest)
    (run_leftExit final messageOffset returnDest rest (by omega) hfRun)
    (by simpa [leftExitCompared] using hfFork)
    (by simp [leftExitLocated, CopyFree])
  have h7 := blockCost_potential rightInitLocated
    (leftExited final messageOffset returnDest rest)
    (rightLoopAt final messageOffset returnDest rest 0)
    (CompressionTrace.run_rightInit final messageOffset returnDest rest
      (by omega) hfRun)
    (by simpa [leftExited] using hfFork)
    (by simp [rightInitLocated, CopyFree])
  have h01 := potential_trans _ _ _ _ _ _ _ h0 h1
  have h012 := potential_trans _ _ _ _ _ _ _ h01 h2
  have h0123 := potential_trans _ _ _ _ _ _ _ h012 h3
  have h01234 := potential_trans _ _ _ _ _ _ _ h0123 h4
  have ht : (gasSteps_leftTest_exit final messageOffset returnDest rest
        (by omega) hfCode hfFork hfRun hfNp).cost +
      MachineState.memCost final.activeWords.toNat =
      Meter.runLocatedBlockStaticCost leftTestLocated +
        MachineState.memCost
          (leftExitCompared final messageOffset returnDest rest).activeWords.toNat := by
    rw [leftTestExit_cost]
    simpa [leftLoopAt] using h5
  have he : (gasSteps_leftExit final messageOffset returnDest rest
        (by omega) hfCode hfFork hfRun hfNp).cost + MachineState.memCost
        (leftExitCompared final messageOffset returnDest rest).activeWords.toNat =
      Meter.runLocatedBlockStaticCost leftExitLocated +
        MachineState.memCost
          (leftExited final messageOffset returnDest rest).activeWords.toNat := by
    rw [leftExit_cost]
    exact h6
  have hr : (CompressionTrace.gasSteps_rightInit final messageOffset returnDest
        rest (by omega) hfCode hfFork hfRun hfNp).cost + MachineState.memCost
        (leftExited final messageOffset returnDest rest).activeWords.toNat =
      Meter.runLocatedBlockStaticCost rightInitLocated +
        MachineState.memCost final.activeWords.toNat := by
    rw [rightInit_cost]
    simpa [rightLoopAt] using h7
  have h01234t := potential_trans _ _ _ _ _ _ _ h01234 ht
  have h01234te := potential_trans _ _ _ _ _ _ _ h01234t he
  have hall := potential_trans _ _ _ _ _ _ _ h01234te hr
  have hshape :
      (gasSteps_compressToRight s messageOffset returnDest rest hstack hcode
        hfork hrun hnp).cost =
      (gasSteps_scheduleSetup s messageOffset returnDest rest (by omega) hcode
        hfork hrun hnp).cost +
      ((Schedule.gasSteps_schedule s messageOffset (UInt256.ofNat 630) tail
        (by simp [tail]; omega) hcode hfork hrun hnp (by decide)).cost +
      ((gasSteps_copyState scheduled messageOffset returnDest rest (by omega)
        hsCode hsFork hsRun hsNp).cost +
      (Stepper.runLocatedBlockCost leftInitLocated
        (copiesReturned scheduled messageOffset returnDest rest) +
      ((gasSteps_left80Concrete initial messageOffset returnDest rest hstack
        hiCode hiFork hiRun hiNp).cost +
      ((gasSteps_leftTest_exit final messageOffset returnDest rest (by omega)
        hfCode hfFork hfRun hfNp).cost +
      ((gasSteps_leftExit final messageOffset returnDest rest (by omega) hfCode
        hfFork hfRun hfNp).cost +
      (CompressionTrace.gasSteps_rightInit final messageOffset returnDest rest
        (by omega) hfCode hfFork hfRun hfNp).cost)))))) := by
    rfl
  rw [hshape]
  change _ = compressToRightWork + MachineState.memCost final.activeWords.toNat
  unfold compressToRightWork
  omega

def compressionWork : Nat := compressToRightWork + rightLoopAndTailWork

theorem compressionWork_eq : compressionWork = ExactGasBridge.compressionWork := by
  rfl

theorem compress_cost_potential (s : State) (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (CompressionFullTrace.gasSteps_compress s input i hcode hfork hrun
      hnp).cost + MachineState.memCost s.activeWords.toNat =
      ExactGasBridge.compressionWork + MachineState.memCost
        (CompressionFullTrace.resultState s input i).activeWords.toNat := by
  let messageOffset := DriverTrace.messageOffsetWord i
  let returnDest := UInt256.ofNat 0x643
  let rest := CompressionFullTrace.driverRest input i
  let leftFinal := leftFinalState s messageOffset returnDest rest
  have hleftCode : leftFinal.executionEnv.code = referenceBytecode := by
    simpa [leftFinal, leftFinalState, leftInitialState, copiedWorkingState,
      copyRegion, scheduledState, leftStates_executionEnv] using hcode
  have hleftFork : leftFinal.fork = .Osaka := by
    simpa [leftFinal, leftFinalState, leftInitialState, copiedWorkingState,
      copyRegion, scheduledState, State.fork] using hfork
  have hleftRun : leftFinal.halt = .Running := by
    simpa [leftFinal, leftFinalState, leftInitialState, copiedWorkingState,
      copyRegion, scheduledState, leftStates_halt] using hrun
  have hleftNp : Precompile.isPrecompile leftFinal.executionEnv.fork
      leftFinal.executionEnv.codeAddr = false := by
    simpa [leftFinal, leftFinalState, leftInitialState, copiedWorkingState,
      copyRegion, scheduledState, leftStates_executionEnv] using hnp
  have hleft := compressToRight_cost_potential s messageOffset returnDest rest
    (by simp [rest, CompressionFullTrace.driverRest]) hcode hfork hrun hnp
  have hright := rightLoopAndTail_cost_potential leftFinal messageOffset
    returnDest rest (by simp [rest, CompressionFullTrace.driverRest])
    hleftCode hleftFork hleftRun hleftNp (by decide)
  have hall := potential_trans _ _ _ _ _ _ _ hleft hright
  have hshape :
      (CompressionFullTrace.gasSteps_compress s input i hcode hfork hrun
        hnp).cost =
      (gasSteps_compressToRight s messageOffset returnDest rest
        (by simp [rest, CompressionFullTrace.driverRest]) hcode hfork hrun
        hnp).cost +
      (CompressionTailTrace.gasSteps_rightLoopAndTail leftFinal messageOffset
        returnDest rest (by simp [rest, CompressionFullTrace.driverRest])
        hleftCode hleftFork hleftRun hleftNp (by decide)).cost := by
    rfl
  rw [hshape]
  change _ = ExactGasBridge.compressionWork + MachineState.memCost
    (CompressionTailTrace.rightTailResult leftFinal messageOffset returnDest
      rest).activeWords.toNat
  rw [← compressionWork_eq]
  exact hall

theorem compressionCostFacts (input : ByteArray) (hfit : CalldataFits input) :
    ExactGasBridge.CompressionCostFacts input
      (CompressionSeamBridge.toCompressionSeam
        (CompressionRunTrace.compressionRun input hfit)) := by
  constructor
  intro i hi
  let s := CompressionRunTrace.states input i
  have hcode : s.executionEnv.code = referenceBytecode := by
    simp [s, PaddingTrace.padReturned_code]
  have hfork : s.fork = .Osaka := by
    rw [State.fork, CompressionRunTrace.states_executionEnv]
    exact PaddingTrace.padReturned_fork input
  have hrun : s.halt = .Running := CompressionRunTrace.states_halt input i
  have hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false := by
    simpa [s, CompressionRunTrace.states_executionEnv] using
      PaddingTrace.padReturned_noPrecompile input
  have h := compress_cost_potential s input i hcode hfork hrun hnp
  simpa [CompressionSeamBridge.toCompressionSeam,
    CompressionRunTrace.compressionRun, s, CompressionRunTrace.states] using h

end Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionGasIntegration
