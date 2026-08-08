import Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionGasIntegration

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionGasIntegration

open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM
open CompressionTrace
open CompressionRightTrace

theorem left80_cost_potential (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_left80Concrete s messageOffset returnDest rest hstack hcode
      hfork hrun hnp).cost + MachineState.memCost s.activeWords.toNat =
      leftLoopWork + MachineState.memCost
        (leftStates s messageOffset returnDest rest 80).activeWords.toNat := by
  unfold gasSteps_left80Concrete gasSteps_left80 leftLoopWork
  apply iterateBounded_cost_potential_sum
  intro i hi
  let q := leftStates s messageOffset returnDest rest i
  have hqcode : q.executionEnv.code = referenceBytecode := by
    rw [leftStates_executionEnv]
    exact hcode
  have hqfork : q.fork = .Osaka := by
    rw [State.fork, leftStates_executionEnv]
    exact hfork
  have hqrun : q.halt = .Running := by rw [leftStates_halt]; exact hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by
    simpa [q, leftStates_executionEnv] using hnp
  simpa [q, leftStates, leftLoopAt] using
    leftIteration_cost_potential q messageOffset returnDest rest i hi hstack
      hqcode hqfork hqrun hqnp

theorem right80_cost_potential (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_right80Concrete s messageOffset returnDest rest hstack hcode
      hfork hrun hnp).cost + MachineState.memCost s.activeWords.toNat =
      rightLoopWork + MachineState.memCost
        (rightStates s messageOffset returnDest rest 80).activeWords.toNat := by
  unfold gasSteps_right80Concrete gasSteps_right80 rightLoopWork
  apply iterateBounded_cost_potential_sum
  intro i hi
  let q := rightStates s messageOffset returnDest rest i
  have hqcode : q.executionEnv.code = referenceBytecode := by
    rw [rightStates_executionEnv]
    exact hcode
  have hqfork : q.fork = .Osaka := by
    rw [State.fork, rightStates_executionEnv]
    exact hfork
  have hqrun : q.halt = .Running := by rw [rightStates_halt]; exact hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by
    simpa [q, rightStates_executionEnv] using hnp
  simpa [q, rightStates, rightLoopAt] using
    rightIteration_cost_potential q messageOffset returnDest rest i hi hstack
      hqcode hqfork hqrun hqnp

end Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionGasIntegration
