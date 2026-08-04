import Challenge.Sha256.Reference.Proofs.Bytecode.RoundT1Gas
import Challenge.Sha256.Reference.Proofs.Bytecode.RoundT2Gas
import Challenge.Sha256.Reference.Proofs.Bytecode.RoundUpdatesGas

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Challenge.Sha256.Reference.Proofs.Bytecode.CompressionGas

open Challenge.Sha256
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

theorem roundIteration_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat)
    (hj : j < 64) (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Compression.gasSteps_roundIteration s msgOff returnDest rest j hj hcap
      hcode hfork hrun hnp).cost + MachineState.memCost
        (Compression.roundAt s msgOff returnDest rest j).activeWords.toNat =
      1799 + MachineState.memCost
        (Compression.afterSecondIteration s msgOff returnDest rest j).activeWords.toNat := by
  have h1 := t1_cost_potential s msgOff returnDest rest j hj hcap hcode
    hfork hrun hnp
  have h2 := t2_cost_potential s msgOff returnDest rest j hcap hcode
    hfork hrun hnp
  have hu := updates_cost_potential s msgOff returnDest rest j hj hcap hcode
    hfork hrun hnp
  unfold Compression.gasSteps_roundIteration
  simp only [Challenge.EvmProof.GasSteps.trans_cost]
  omega

theorem roundLoop_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Compression.gasSteps_roundLoop s msgOff returnDest rest hcap hcode hfork
      hrun hnp).cost + MachineState.memCost
        (Compression.roundLoopState s msgOff returnDest rest 0).activeWords.toNat =
      64 * 1799 + MachineState.memCost
        (Compression.roundLoopState s msgOff returnDest rest 64).activeWords.toNat := by
  unfold Compression.gasSteps_roundLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add 64 1799
  intro i hi
  let q := Compression.roundLoopState s msgOff returnDest rest i
  have qcode : q.executionEnv.code = referenceBytecode := by
    simpa [q] using hcode
  have qfork : q.fork = .Osaka := by
    simpa [q, State.fork] using hfork
  have qrun : q.halt = .Running := by
    simpa [q] using hrun
  have qnp : Precompile.isPrecompile q.executionEnv.fork
      q.executionEnv.codeAddr = false := by
    simpa [q] using hnp
  have h := roundIteration_cost_potential q msgOff returnDest rest i hi hcap
    qcode qfork qrun qnp
  dsimp only [q] at h
  have h' :
      (Compression.gasSteps_roundIteration
        (Compression.roundLoopState s msgOff returnDest rest i)
        msgOff returnDest rest i hi hcap qcode qfork qrun qnp).cost +
          MachineState.memCost
            (Compression.roundLoopState s msgOff returnDest rest i).activeWords.toNat =
        1799 + MachineState.memCost
          (Compression.roundLoopState s msgOff returnDest rest (i + 1)).activeWords.toNat := by
    simpa [Compression.roundAt, Compression.roundLoopState] using h
  simpa only [Challenge.EvmProof.GasSteps.cast_cost] using h'

end Challenge.Sha256.Reference.Proofs.Bytecode.CompressionGas

