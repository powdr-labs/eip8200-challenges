import Challenge.Sha256.Reference.Proofs.Bytecode.CompressionGasBase

/-! Exact gas summaries for entering compression and copying the hash state. -/

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Challenge.Sha256.Reference.Proofs.Bytecode.CompressionGas

open Challenge.Sha256
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

theorem entry_cost_potential (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Compression.gasSteps_entry s msgOff returnDest rest hcap hcode hfork
      hrun hnp).cost + MachineState.memCost
        (Compression.compressEntry s msgOff returnDest rest).activeWords.toNat =
      18 + MachineState.memCost
        (Compression.callSchedule s msgOff returnDest rest).activeWords.toNat := by
  have hresult := Compression.run_entry s msgOff returnDest rest (by omega)
    hcode hrun
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    Compression.entryPath hresult
    (by simpa [Compression.compressEntry, State.fork] using hfork) (by
      intro located hmem q hq
      simp [Compression.entryPath] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl <;>
        simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hq])
  unfold Compression.gasSteps_entry
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simpa [Compression.compressEntry, Compression.callSchedule,
    Schedule.scheduleEntry, Compression.entryPath,
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
    Challenge.EvmProof.Meter.instrStaticCost, Gas.baseCost] using hmeter

private theorem copyWork (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Meter.runLocatedBlockCostWithoutMemory
      Compression.copyAndLoopStartPath
      { s with pc := UInt256.ofNat 621
               stack := [msgOff, returnDest] ++ rest } = 39 := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [Challenge.EvmProof.Meter.runLocatedBlockCostWithoutMemory,
    Challenge.EvmProof.Meter.instrCostWithoutMemory,
    Compression.copyAndLoopStartPath,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, Gas.baseCost, Gas.copyWordCost,
    hc2, hc3, hc4, hc5, hrun, State.activeWordsAfterUInt256_2]

theorem copy_cost_potential (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost
        Compression.copyAndLoopStartPath
        { s with pc := UInt256.ofNat 621
                 stack := [msgOff, returnDest] ++ rest } +
      MachineState.memCost s.activeWords.toNat =
      39 + MachineState.memCost
        (Compression.roundAt (Compression.copyHashState s)
          msgOff returnDest rest 0).activeWords.toNat := by
  have hresult := Compression.run_copyAndLoopStart s msgOff returnDest rest
    hcap hrun
  have h := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential
    Compression.copyAndLoopStartPath hresult
  rw [copyWork s msgOff returnDest rest hcap hrun] at h
  simpa using h

end Challenge.Sha256.Reference.Proofs.Bytecode.CompressionGas
