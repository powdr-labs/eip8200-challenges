import Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverState
import Challenge.EvmProof.FixedPathGas

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverCorrect

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof Challenge.EvmProof.Stepper Challenge.EvmProof.Meter

private def copyPrePath := DriverBlocks.fullBlockCallPath.take 4
private def copyInstructionPath :=
  (DriverBlocks.fullBlockCallPath.drop 4).take 1
private def copyPostPath := DriverBlocks.fullBlockCallPath.drop 5

private def copyPreState (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) : State := { s with
  pc := UInt256.ofNat 2472
  stack := [UInt256.ofNat 288, off, UInt256.ofNat 64,
    off, endWord, rem, n] ++ rest }

private def copyInstructionState (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) : State := { s with
  pc := UInt256.ofNat 2473
  activeWords := UInt256.ofNat 140
  memory := MachineState.writeBytes s.memory
    (MachineState.readPadded s.executionEnv.calldata off.toNat 64) 288
  stack := [off, endWord, rem, n] ++ rest }

private noncomputable def copyPreTrace (s : State)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2465)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s (copyPreState s off endWord rem n rest) :=
  let hresult : runLocatedBlock copyPrePath s =
      some (copyPreState s off endWord rem n rest) := by
    unfold copyPrePath
    have hcap' : rest.length < 1000 := by omega
    evm_block hcap'; simp [copyPreState, hrun]
  Challenge.EvmProof.FixedPathGas.trace copyPrePath 10 (by rfl) (by rfl)
    (by simpa [Loop.art] using hcode) hfork hresult hrun hnp
    (by simp [copyPreState, haw])

private noncomputable def copyInstructionTrace (s : State)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (copyPreState s off endWord rem n rest)
      (copyInstructionState s off endWord rem n rest) :=
  let hresult : runLocatedBlock copyInstructionPath
      (copyPreState s off endWord rem n rest) =
      some (copyInstructionState s off endWord rem n rest) := by
    unfold copyInstructionPath
    have hcap' : rest.length < 1000 := by omega
    have hc : rest.length ≤ 1016 := by omega
    evm_block hcap';
      simp_all [copyPreState, copyInstructionState,
        MachineState.activeWordsAfter]
  let raw := runLocatedBlock_sound Loop.art .Osaka copyInstructionPath
    (by simpa [copyPreState, Loop.art] using hcode)
    (by simpa [copyPreState] using hfork) hresult
    (by simpa [copyPreState] using hrun)
    (by simpa [copyPreState] using hnp)
  GasSteps.reprice raw 9 (by
    rw [runLocatedBlock_sound_cost]
    simp [copyInstructionPath, DriverBlocks.fullBlockCallPath,
      runLocatedBlockCost, instrCost, Gas.totalCost, Gas.baseCost,
      Gas.copyWordCost, Gas.calldatacopyTotal,
      MachineState.memExpansionDelta, MachineState.activeWordsAfter,
      MachineState.memCost, copyPreState, haw])

private noncomputable def copyPostTrace (s : State)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (copyInstructionState s off endWord rem n rest)
      (copiedState s off endWord rem n rest) :=
  let hresult : runLocatedBlock copyPostPath
      (copyInstructionState s off endWord rem n rest) =
      some (copiedState s off endWord rem n rest) := by
    unfold copyPostPath
    have hcap' : rest.length < 1000 := by omega
    have hc : rest.length ≤ 1019 := by omega
    have hc' : rest.length ≤ 1018 := by omega
    have hc'' : rest.length ≤ 1017 := by omega
    have hbody : Decode.isValidJumpDest Loop.bytes 4 = true := by
      have h := ProgramArtifact.isValidJumpDest_index Loop.art 2 (by rfl)
      change Decode.isValidJumpDest Loop.bytes 4 = true at h
      exact h
    evm_block hcap';
      simp_all [copyInstructionState, copiedState]
  Challenge.EvmProof.FixedPathGas.trace copyPostPath 14 (by rfl) (by rfl)
    (by simpa [copyInstructionState, Loop.art] using hcode)
    (by simpa [copyInstructionState] using hfork) hresult
    (by simpa [copyInstructionState] using hrun)
    (by simpa [copyInstructionState] using hnp) rfl

noncomputable def gasSteps_copy (s : State)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2465)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s (copiedState s off endWord rem n rest) :=
  GasSteps.transKnown
    (copyPreTrace s off endWord rem n rest hcap haw hcode hfork hrun hpc
      hstack hnp)
    (GasSteps.transKnown
      (copyInstructionTrace s off endWord rem n rest hcap haw hcode hfork
        hrun hnp)
      (copyPostTrace s off endWord rem n rest hcap hcode hfork hrun hnp)
      9 14 rfl rfl)
    10 23 rfl rfl

@[simp] theorem gasSteps_copy_cost (s : State)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2465)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (gasSteps_copy s off endWord rem n rest hcap haw hcode hfork hrun hpc
      hstack hnp).cost = 33 := rfl

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverCorrect
