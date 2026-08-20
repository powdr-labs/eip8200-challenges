import Challenge.Sha256.Submissions.Sha256Fast.Proofs.RoundCorrect
import Challenge.Sha256.Submissions.Sha256Fast.Proofs.FeedForwardCorrect
import Challenge.Sha256.Submissions.Sha256Fast.Proofs.ScheduleTrace
import Challenge.Sha256.Submissions.Sha256Fast.Proofs.GasTools

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.CompressionCorrect

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof Challenge.EvmProof.Stepper Challenge.EvmProof.Word
open MemoryCorrect

namespace Ref

abbrev workingOfArray :=
  Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect.workingOfArray

abbrev compressBlock_eq_feedForward :=
  Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect.compressBlock_eq_feedForward

end Ref

def working (H : Array UInt32) (block : ByteArray) : Ref.Working :=
  Ref.rounds (Ref.workingOfArray H) block 288 64

def finalState (s : State) (H : Array UInt32) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  let scheduled := ScheduleTrace.exitState s returnDest rest
  let x := working H s.memory
  { scheduled with
    pc := returnDest
    activeWords := UInt256.ofNat 140
    memory := DriverBlocks.foldedMemory scheduled.memory
      x.a x.b x.c x.d x.e x.f x.g x.h
      H[0]! H[1]! H[2]! H[3]! H[4]! H[5]! H[6]! H[7]!
    stack := rest }

private noncomputable def initialScheduleTrace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock Loop.Body.initialSchedulePath s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace Loop.Body.initialSchedulePath 420
    (by rfl) (by rfl) (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

private noncomputable def prepareRoundsTrace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock Loop.Body.prepareRoundsPath s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace Loop.Body.prepareRoundsPath 53
    (by rfl) (by rfl) (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

/-- One call of the bytecode compression body implements one mathematical
SHA-256 compression block over the 64-byte staging window at memory offset
288. -/
noncomputable def gasSteps_compressBlock (s : State) (H : Array UInt32)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 989)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hret : Decode.isValidJumpDest Loop.bytes returnDest.toNat = true)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 4)
    (hstack : s.stack = returnDest :: rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hH : HashCorrect s.memory H)
    (hK : ConstantsCorrect s.memory) :
    GasSteps s (finalState s H returnDest rest) := by
  let initial := Ref.workingOfArray H
  let x := working H s.memory
  let scheduled := ScheduleTrace.exitState s returnDest rest
  let prepared := RoundCorrect.groupEntry scheduled initial s.memory 288 0
    (returnDest :: rest)
  let folded := RoundCorrect.foldEntry scheduled initial s.memory 288
    (returnDest :: rest)
  have rInitial : runLocatedBlock Loop.Body.initialSchedulePath s =
      some (ScheduleTrace.entry s returnDest rest 0) := by
    simpa [ScheduleTrace.entry, ScheduleCorrect.initialMemory] using
      ScheduleCorrect.run_initialSchedule s returnDest rest (by omega)
        haw hrun hpc hstack
  let gInitial := initialScheduleTrace hcode hfork rInitial hrun hnp
    (by simp [ScheduleTrace.entry, haw])
  let gSchedule := ScheduleTrace.gasSteps_schedule s returnDest rest
    (by omega) hcode hfork hrun hnp
  have hHScheduled : HashCorrect scheduled.memory H := by
    simpa [scheduled, ScheduleTrace.exitState] using
      MemoryCorrect.hash_writeSchedule s.memory s.memory 288 H hH 64
  have hKScheduled : ConstantsCorrect scheduled.memory := by
    simpa [scheduled, ScheduleTrace.exitState] using
      MemoryCorrect.constants_writeSchedule s.memory s.memory 288 hK 64 (by omega)
  have hWScheduled : ScheduleCorrect.WCorrect scheduled.memory s.memory 288 64 := by
    simpa [scheduled, ScheduleTrace.exitState] using
      ScheduleCorrect.writeSchedule_correct s.memory s.memory 288 64
  have rPrepare : runLocatedBlock Loop.Body.prepareRoundsPath scheduled =
      some prepared := by
    have hread (i : Nat) (hi : i < 8) :
        MachineState.readWord scheduled.memory (32 + 32 * i) =
          ofUInt32 H[i]! := by
      simpa [hValue, hOffset, Nat.mul_comm] using hHScheduled i hi
    have r := Loop.Body.run_prepareRounds scheduled
      (ofUInt32 H[0]!) (ofUInt32 H[1]!) (ofUInt32 H[2]!) (ofUInt32 H[3]!)
      (ofUInt32 H[4]!) (ofUInt32 H[5]!) (ofUInt32 H[6]!) (ofUInt32 H[7]!)
      returnDest rest (by omega) (by simp [scheduled, ScheduleTrace.exitState])
      (by simpa [scheduled, ScheduleTrace.exitState] using hrun) rfl rfl
      (hread 0 (by omega)) (hread 1 (by omega)) (hread 2 (by omega))
      (hread 3 (by omega)) (hread 4 (by omega)) (hread 5 (by omega))
      (hread 6 (by omega)) (hread 7 (by omega))
    simpa [prepared, RoundCorrect.groupEntry, RoundCorrect.roundState,
      RoundCorrect.phaseStack, initial, Ref.workingOfArray,
      MemoryCorrect.Ref.rounds,
      Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect.rounds,
      Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect.workingOfArray]
      using r
  let gPrepare := prepareRoundsTrace
    (by simpa [scheduled, ScheduleTrace.exitState, Loop.art] using hcode)
    (by simpa [scheduled, ScheduleTrace.exitState] using hfork)
    rPrepare (by simpa [scheduled, ScheduleTrace.exitState] using hrun)
    (by simpa [scheduled, ScheduleTrace.exitState] using hnp) rfl
  let gRounds : GasSteps prepared folded := by
    simpa [prepared, folded] using
      RoundCorrect.gasSteps_rounds scheduled initial s.memory 288
        (returnDest :: rest) (by simp; omega)
        (by simpa [scheduled, ScheduleTrace.exitState] using hcode)
        (by simpa [scheduled, ScheduleTrace.exitState] using hfork)
        (by simpa [scheduled, ScheduleTrace.exitState] using hrun)
        (by simpa [scheduled, ScheduleTrace.exitState] using hnp)
        hKScheduled hWScheduled
  let gFold : GasSteps folded (finalState s H returnDest rest) := by
    have g := FeedForwardCorrect.gasSteps_feedForward folded x H returnDest rest
      (by omega) (by simp [folded, RoundCorrect.foldEntry,
        RoundCorrect.roundState])
      (by simpa [folded, RoundCorrect.foldEntry, RoundCorrect.roundState,
        scheduled, ScheduleTrace.exitState] using hcode)
      (by simpa [folded, RoundCorrect.foldEntry, RoundCorrect.roundState,
        scheduled, ScheduleTrace.exitState] using hfork)
      hret
      (by simpa [folded, RoundCorrect.foldEntry, RoundCorrect.roundState,
        scheduled, ScheduleTrace.exitState] using hrun)
      rfl rfl
      (by simpa [folded, RoundCorrect.foldEntry, RoundCorrect.roundState,
        scheduled, ScheduleTrace.exitState] using hnp)
      (by simpa [folded, RoundCorrect.foldEntry, RoundCorrect.roundState]
        using hHScheduled)
    exact GasSteps.cast g rfl (by
      simp [finalState, folded, scheduled, x, working,
        RoundCorrect.foldEntry, RoundCorrect.roundState,
        RoundCorrect.phaseStack])
  have hRounds : gRounds.cost = 13479 := by
    simp [gRounds, prepared, folded]
  have hFold : gFold.cost = 178 := by
    simp only [gFold]
    exact FeedForwardCorrect.gasSteps_feedForward_cost folded x H returnDest rest
      (by omega) (by simp [folded, RoundCorrect.foldEntry,
        RoundCorrect.roundState])
      (by simpa [folded, RoundCorrect.foldEntry, RoundCorrect.roundState,
        scheduled, ScheduleTrace.exitState] using hcode)
      (by simpa [folded, RoundCorrect.foldEntry, RoundCorrect.roundState,
        scheduled, ScheduleTrace.exitState] using hfork)
      hret
      (by simpa [folded, RoundCorrect.foldEntry, RoundCorrect.roundState,
        scheduled, ScheduleTrace.exitState] using hrun)
      rfl rfl
      (by simpa [folded, RoundCorrect.foldEntry, RoundCorrect.roundState,
        scheduled, ScheduleTrace.exitState] using hnp)
      (by simpa [folded, RoundCorrect.foldEntry, RoundCorrect.roundState]
        using hHScheduled)
  let right := GasSteps.transKnown gRounds gFold 13479 178 hRounds hFold
  let right := GasSteps.transKnown gPrepare right 53 13657 rfl rfl
  let right := GasSteps.transKnown gSchedule right 7037 13710
    (ScheduleTrace.gasSteps_schedule_cost s returnDest rest (by omega)
      hcode hfork hrun hnp) rfl
  exact GasSteps.transKnown gInitial right 420 20747 rfl rfl

@[simp] theorem gasSteps_compressBlock_cost (s : State) (H : Array UInt32)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 989)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hret : Decode.isValidJumpDest Loop.bytes returnDest.toNat = true)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 4)
    (hstack : s.stack = returnDest :: rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hH : HashCorrect s.memory H)
    (hK : ConstantsCorrect s.memory) :
    (gasSteps_compressBlock s H returnDest rest hcap haw hcode hfork hret hrun
      hpc hstack hnp hH hK).cost = 21167 := rfl

theorem finalState_hash (s : State) (H : Array UInt32)
    (returnDest : UInt256) (rest : List UInt256) :
    HashCorrect (finalState s H returnDest rest).memory
      (Sha256.compressBlock H s.memory 288) := by
  have h := MemoryCorrect.folded_hash
    (ScheduleTrace.exitState s returnDest rest).memory H (working H s.memory)
  rw [Ref.compressBlock_eq_feedForward H s.memory 288]
  simpa [finalState, working] using h

theorem finalState_constants (s : State) (H : Array UInt32)
    (returnDest : UInt256) (rest : List UInt256)
    (hK : ConstantsCorrect s.memory) :
    ConstantsCorrect (finalState s H returnDest rest).memory := by
  apply MemoryCorrect.folded_constants
  simpa [ScheduleTrace.exitState] using
    MemoryCorrect.constants_writeSchedule s.memory s.memory 288 hK 64 (by omega)

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.CompressionCorrect
