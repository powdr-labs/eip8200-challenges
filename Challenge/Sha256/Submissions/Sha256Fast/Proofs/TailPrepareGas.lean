import Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailState
import Challenge.Sha256.Submissions.Sha256Fast.Proofs.GasTools

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailPrepareGas

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof Challenge.EvmProof.Stepper Challenge.EvmProof.Meter
open TailState

private def prePath := DriverBlocks.tailPreparePath.take 4
private def copyPath := (DriverBlocks.tailPreparePath.drop 4).take 1
private def postPath := DriverBlocks.tailPreparePath.drop 5

private def preState (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) : State := { s with
  pc := UInt256.ofNat 2498
  stack := [UInt256.ofNat 288, off, UInt256.ofNat 64,
    off, endWord, rem, n] ++ rest }

private def copyState (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) : State := { s with
  pc := UInt256.ofNat 2499
  activeWords := UInt256.ofNat 140
  memory := MachineState.writeBytes s.memory
    (MachineState.readPadded s.executionEnv.calldata off.toNat 64) 288
  stack := [off, endWord, rem, n] ++ rest }

private noncomputable def preTrace (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 985)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2491)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s (preState s off endWord rem n rest) :=
  let hresult : runLocatedBlock prePath s =
      some (preState s off endWord rem n rest) := by
    unfold prePath
    have hcap' : rest.length < 1000 := by omega
    evm_block hcap'; simp [preState, hrun]
  FixedPathGas.trace prePath 10 (by rfl) (by rfl)
    (by simpa [Loop.art] using hcode) hfork hresult hrun hnp
    (by simp [preState, haw])

private noncomputable def copyTrace (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 985)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (preState s off endWord rem n rest)
      (copyState s off endWord rem n rest) :=
  let hresult : runLocatedBlock copyPath (preState s off endWord rem n rest) =
      some (copyState s off endWord rem n rest) := by
    unfold copyPath
    have hcap' : rest.length < 1000 := by omega
    have hc : rest.length ≤ 1016 := by omega
    evm_block hcap';
      simp_all [preState, copyState, MachineState.activeWordsAfter]
  let raw := runLocatedBlock_sound Loop.art .Osaka copyPath
    (by simpa [preState, Loop.art] using hcode)
    (by simpa [preState] using hfork) hresult
    (by simpa [preState] using hrun) (by simpa [preState] using hnp)
  GasSteps.reprice raw 9 (by
    rw [runLocatedBlock_sound_cost]
    simp [copyPath, DriverBlocks.tailPreparePath, runLocatedBlockCost, instrCost,
      Gas.totalCost, Gas.baseCost, Gas.copyWordCost, Gas.calldatacopyTotal,
      MachineState.memExpansionDelta, MachineState.activeWordsAfter,
      MachineState.memCost, preState, haw])

private noncomputable def postTrace (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 985) (hrem : rem.toNat < 64)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (copyState s off endWord rem n rest)
      (prepared s off endWord rem n rest) :=
  let hresult : runLocatedBlock postPath (copyState s off endWord rem n rest) =
      some (prepared s off endWord rem n rest) := by
    unfold postPath
    have hcap' : rest.length < 1000 := by omega
    have hc : rest.length ≤ 1019 := by omega
    have hc18 : rest.length ≤ 1018 := by omega
    have hc17 : rest.length ≤ 1017 := by omega
    have hc16 : rest.length ≤ 1016 := by omega
    evm_block hcap'
    have hadd : (UInt256.ofNat 288 + rem).toNat = 288 + rem.toNat := by
      rw [Challenge.EvmProof.Word.word_toNat_add,
        Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      norm_num
    simp [copyState, prepared, hrun, hadd, hc, hc18, hc17, hc16]
    apply congrArg UInt256.ofNat
    norm_num [MachineState.activeWordsAfter, hadd]
    omega
  FixedPathGas.trace postPath 27 (by rfl) (by rfl)
    (by simpa [copyState, Loop.art] using hcode)
    (by simpa [copyState] using hfork) hresult
    (by simpa [copyState] using hrun) (by simpa [copyState] using hnp) rfl

noncomputable def gasSteps_prepare (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 985)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2491)
    (hrem : rem.toNat < 64)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s (prepared s off endWord rem n rest) :=
  GasSteps.transKnown
    (preTrace s off endWord rem n rest hcap haw hcode hfork hrun hpc hstack hnp)
    (GasSteps.transKnown
      (copyTrace s off endWord rem n rest hcap haw hcode hfork hrun hnp)
      (postTrace s off endWord rem n rest hcap hrem hcode hfork hrun hnp)
      9 27 rfl rfl)
    10 36 rfl rfl

@[simp] theorem gasSteps_prepare_cost (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 985)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2491)
    (hrem : rem.toNat < 64)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (gasSteps_prepare s off endWord rem n rest hcap haw hcode hfork hrun hpc hrem
      hstack hnp).cost = 46 := rfl

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailPrepareGas
