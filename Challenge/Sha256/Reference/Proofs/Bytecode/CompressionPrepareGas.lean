import Challenge.Sha256.Reference.Proofs.Bytecode.CompressionEntryGas
import Challenge.Sha256.Reference.Proofs.Bytecode.ScheduleGas

/-! Exact gas summary for the complete compression preparation phase. -/

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Challenge.Sha256.Reference.Proofs.Bytecode.CompressionGas

open Challenge.Sha256
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

private theorem prepare_chain (cEntry cSchedule cCopy p₀ p₁ p₂ p₃ : Nat)
    (hentry : cEntry + p₀ = 18 + p₁)
    (hschedule : cSchedule + p₁ = 39162 + p₂)
    (hcopy : cCopy + p₂ = 39 + p₃) :
    (cEntry + (cSchedule + cCopy)) + p₀ = 39219 + p₃ := by
  omega

theorem prepare_parts_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (@Challenge.EvmProof.GasSteps.cost
      (Compression.compressEntry s msgOff returnDest rest)
      (Compression.callSchedule s msgOff returnDest rest)
      (Compression.gasSteps_entry s msgOff returnDest rest hcap hcode hfork
        hrun hnp) +
      (Schedule.gasSteps_scheduleCost s msgOff (UInt256.ofNat 621)
        (msgOff :: returnDest :: rest)
        (Compression.scheduleCallStackCap msgOff returnDest rest hcap)
        hcode hfork hrun hnp Compression.scheduleCallReturnValid +
       Challenge.EvmProof.Stepper.runLocatedBlockCost
        Compression.copyAndLoopStartPath
        { Compression.afterSchedule s msgOff returnDest rest with
          pc := UInt256.ofNat 621
          stack := [msgOff, returnDest] ++ rest })) +
      MachineState.memCost
        (Compression.compressEntry s msgOff returnDest rest).activeWords.toNat =
    39219 + MachineState.memCost
      (Compression.roundAt
        (Compression.copyHashState
          (Compression.afterSchedule s msgOff returnDest rest))
        msgOff returnDest rest 0).activeWords.toNat := by
  have hentry := entry_cost_potential s msgOff returnDest rest hcap hcode
    hfork hrun hnp
  have hschedule :
      Schedule.gasSteps_scheduleCost s msgOff (UInt256.ofNat 621)
        (msgOff :: returnDest :: rest)
        (Compression.scheduleCallStackCap msgOff returnDest rest hcap)
        hcode hfork hrun hnp Compression.scheduleCallReturnValid +
          MachineState.memCost
            (Schedule.scheduleEntry s msgOff (UInt256.ofNat 621)
              (msgOff :: returnDest :: rest)).activeWords.toNat =
      39162 + MachineState.memCost
        (Schedule.scheduleResult s msgOff (UInt256.ofNat 621)
          (msgOff :: returnDest :: rest)).activeWords.toNat := by
    exact ScheduleGas.schedule_cost_potential s msgOff (UInt256.ofNat 621)
      (msgOff :: returnDest :: rest)
      (Compression.scheduleCallStackCap msgOff returnDest rest hcap)
      hcode hfork hrun hnp Compression.scheduleCallReturnValid
  have qrun : (Compression.afterSchedule s msgOff returnDest rest).halt =
      .Running := by simpa using hrun
  have hcopy := copy_cost_potential
    (Compression.afterSchedule s msgOff returnDest rest) msgOff returnDest rest
    (by omega) qrun
  exact prepare_chain _ _ _ _ _ _ _ hentry hschedule hcopy

theorem prepare_cost_potential (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    @Challenge.EvmProof.GasSteps.cost
      (Compression.compressEntry s msgOff returnDest rest)
      (Compression.roundAt
        (Compression.copyHashState
          (Compression.afterSchedule s msgOff returnDest rest))
        msgOff returnDest rest 0)
      (Compression.gasSteps_toRoundLoop s msgOff returnDest rest hcap hcode
        hfork hrun hnp) + MachineState.memCost
          (Compression.compressEntry s msgOff returnDest rest).activeWords.toNat =
      39219 + MachineState.memCost
        (Compression.roundAt
          (Compression.copyHashState
            (Compression.afterSchedule s msgOff returnDest rest))
          msgOff returnDest rest 0).activeWords.toNat := by
  have hparts := prepare_parts_cost_potential s msgOff returnDest rest hcap
    hcode hfork hrun hnp
  rw [Compression.gasSteps_toRoundLoop_cost]
  exact hparts

end Challenge.Sha256.Reference.Proofs.Bytecode.CompressionGas
