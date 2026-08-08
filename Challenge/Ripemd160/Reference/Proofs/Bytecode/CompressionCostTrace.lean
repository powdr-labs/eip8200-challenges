import Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionFullTrace
import Challenge.Ripemd160.Reference.Proofs.Bytecode.ExactGasBridge
import Challenge.EvmProof.Meter

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# Exact potential cost of the RIPEMD-160 compressor

Memory expansion is accounted for with the shared `Meter` potential.  Each
straight-line trace contributes only its non-memory work; transitivity then
telescopes all intermediate memory costs.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionCostTrace

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open CompressionTrace
open CompressionRightTrace
open CompressionTailTrace

def CopyFree : Instr → Prop
  | .op .CALLDATACOPY => False
  | .op .MCOPY => False
  | _ => True

private theorem noMemoryCost_eq_static (instruction : Instr) (s : State)
    (fork : Fork) (hfork : s.fork = fork) (hfree : CopyFree instruction) :
    Meter.instrCostWithoutMemory instruction s =
      Meter.instrStaticCost fork instruction := by
  cases instruction with
  | push width value =>
      simp [Meter.instrCostWithoutMemory, Meter.instrStaticCost, hfork]
  | op op =>
      cases op with
      | StopArith op => cases op <;>
          simp [Meter.instrCostWithoutMemory, Meter.instrStaticCost, hfork]
      | CompBit op => cases op <;>
          simp [Meter.instrCostWithoutMemory, Meter.instrStaticCost, hfork]
      | Keccak op => cases op
                     simp [Meter.instrCostWithoutMemory, Meter.instrStaticCost, hfork]
      | Env op => cases op <;> simp [CopyFree, Meter.instrCostWithoutMemory,
          Meter.instrStaticCost, hfork] at hfree ⊢
      | Block op => cases op <;>
          simp [Meter.instrCostWithoutMemory, Meter.instrStaticCost, hfork]
      | StackMemFlow op => cases op <;> simp [CopyFree,
          Meter.instrCostWithoutMemory, Meter.instrStaticCost, hfork] at hfree ⊢
      | Push op => cases op
                   simp [Meter.instrCostWithoutMemory, Meter.instrStaticCost, hfork]
      | Dup op => cases op
                  simp [Meter.instrCostWithoutMemory, Meter.instrStaticCost, hfork]
      | Swap op => cases op
                   simp [Meter.instrCostWithoutMemory, Meter.instrStaticCost, hfork]
      | DupN op => cases op
                   simp [Meter.instrCostWithoutMemory, Meter.instrStaticCost, hfork]
      | SwapN op => cases op
                    simp [Meter.instrCostWithoutMemory, Meter.instrStaticCost, hfork]
      | Exchange op => cases op
                       simp [Meter.instrCostWithoutMemory, Meter.instrStaticCost, hfork]
      | Log op => cases op
                  simp [Meter.instrCostWithoutMemory, Meter.instrStaticCost, hfork]
      | System op => cases op <;>
          simp [Meter.instrCostWithoutMemory, Meter.instrStaticCost, hfork]

private theorem soundBlock_cost_potential
    {artifact : ProgramArtifact} {fork : Fork}
    (path : List (Stepper.Located artifact fork)) (s t : State)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hresult : Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hfree : ∀ located ∈ path, CopyFree located.instruction) :
    (Stepper.runLocatedBlock_sound artifact fork path hcode hfork hresult hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      Meter.runLocatedBlockStaticCost path +
        MachineState.memCost t.activeWords.toNat := by
  rw [Stepper.runLocatedBlock_sound_cost]
  apply Meter.runLocatedBlock_cost_static_potential path hresult hfork
  intro located hmem q hq
  exact noMemoryCost_eq_static located.instruction q fork hq
    (hfree located hmem)

theorem blockCost_potential
    {artifact : ProgramArtifact} {fork : Fork}
    (path : List (Stepper.Located artifact fork)) (s t : State)
    (hresult : Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = fork)
    (hfree : ∀ located ∈ path, CopyFree located.instruction) :
    Stepper.runLocatedBlockCost path s +
        MachineState.memCost s.activeWords.toNat =
      Meter.runLocatedBlockStaticCost path +
        MachineState.memCost t.activeWords.toNat := by
  apply Meter.runLocatedBlock_cost_static_potential path hresult hfork
  intro located hmem q hq
  exact noMemoryCost_eq_static located.instruction q fork hq
    (hfree located hmem)

private theorem potential_trans
    (cost₁ work₁ cost₂ work₂ p₀ p₁ p₂ : Nat)
    (h₁ : cost₁ + p₀ = work₁ + p₁)
    (h₂ : cost₂ + p₁ = work₂ + p₂) :
    (cost₁ + cost₂) + p₀ = (work₁ + work₂) + p₂ := by
  omega

def tailWork : Nat :=
  Meter.runLocatedBlockStaticCost combination0Located +
  Meter.runLocatedBlockStaticCost combination1Located +
  Meter.runLocatedBlockStaticCost combination2Located +
  Meter.runLocatedBlockStaticCost combination3Located +
  Meter.runLocatedBlockStaticCost combination4Located +
  Meter.runLocatedBlockStaticCost combinationPopsLocated +
  Meter.runLocatedBlockStaticCost combinationJumpLocated

theorem tailWork_eq : tailWork = 245 := by rfl

def tableAtWork : Nat := Meter.runLocatedBlockStaticCost TableTrace.tableAtPath
def xAtWork : Nat := Meter.runLocatedBlockStaticCost TableTrace.xAtPath
def wordSetWork : Nat := Meter.runLocatedBlockStaticCost TableTrace.hSetPath

theorem tableAtWork_eq : tableAtWork = 57 := by rfl
theorem xAtWork_eq : xAtWork = 37 := by rfl
theorem wordSetWork_eq : wordSetWork = 42 := by rfl

theorem tableAt_cost_potential (s : State) (base i returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (TableTrace.gasSteps_tableAt s base i returnDest rest hstack hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      tableAtWork + MachineState.memCost
        (TableTrace.tableAtReturned s base i returnDest rest).activeWords.toNat := by
  have hraw := blockCost_potential TableTrace.tableAtPath
    (TableTrace.tableAtEntry s base i returnDest rest)
    (TableTrace.tableAtReturned s base i returnDest rest)
    (TableTrace.run_tableAt s base i returnDest rest hstack hcode hrun hvalid)
    (by simpa [TableTrace.tableAtEntry] using hfork)
    (by simp [TableTrace.tableAtPath, CopyFree])
  simpa [TableTrace.gasSteps_tableAt, TableTrace.tableAtEntry, tableAtWork]
    using hraw

theorem xAt_cost_potential (s : State) (i returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1018)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (TableTrace.gasSteps_xAt s i returnDest rest hstack hcode hfork hrun hnp
      hvalid).cost + MachineState.memCost s.activeWords.toNat =
      xAtWork + MachineState.memCost
        (TableTrace.atReturned s (UInt256.ofNat 0x2a0) i returnDest rest).activeWords.toNat := by
  have hraw := blockCost_potential TableTrace.xAtPath
    (TableTrace.atEntry s (UInt256.ofNat 0x4b) i returnDest rest)
    (TableTrace.atReturned s (UInt256.ofNat 0x2a0) i returnDest rest)
    (TableTrace.run_xAt s i returnDest rest hstack hcode hrun hvalid)
    (by simpa [TableTrace.atEntry] using hfork)
    (by simp [TableTrace.xAtPath, CopyFree])
  simpa [TableTrace.gasSteps_xAt, TableTrace.atEntry, xAtWork] using hraw

theorem wordSet_cost_potential (s : State)
    (base i value returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (TableTrace.gasSteps_wordSet s base i value returnDest rest hstack hcode
      hfork hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      wordSetWork + MachineState.memCost
        (TableTrace.setReturned s base i value returnDest rest).activeWords.toNat := by
  have hraw := blockCost_potential TableTrace.hSetPath
    (TableTrace.setEntry s base i value returnDest rest)
    (TableTrace.setReturned s base i value returnDest rest)
    (TableTrace.run_wordSet s base i value returnDest rest hstack hcode hrun hvalid)
    (by simpa [TableTrace.setEntry] using hfork)
    (by simp [TableTrace.hSetPath, CopyFree])
  simpa [TableTrace.gasSteps_wordSet, TableTrace.setEntry, wordSetWork] using hraw

def scheduleSetupWork : Nat :=
  Meter.runLocatedBlockStaticCost scheduleSetupLocated

theorem scheduleSetupWork_eq : scheduleSetupWork = 18 := by rfl

theorem scheduleSetup_cost_potential (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_scheduleSetup s messageOffset returnDest rest hstack hcode hfork
      hrun hnp).cost + MachineState.memCost s.activeWords.toNat =
      scheduleSetupWork + MachineState.memCost
        (scheduleEntry s messageOffset returnDest rest).activeWords.toNat := by
  have hraw := blockCost_potential scheduleSetupLocated
    (compressEntry s messageOffset returnDest rest)
    (scheduleEntry s messageOffset returnDest rest)
    (run_scheduleSetup s messageOffset returnDest rest hstack hcode hrun)
    (by simpa [compressEntry] using hfork)
    (by simp [scheduleSetupLocated, CopyFree])
  simpa [gasSteps_scheduleSetup, compressEntry, scheduleSetupWork] using hraw

def copyStateWork : Nat := 82

theorem copyState_cost_potential (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_copyState s messageOffset returnDest rest hstack hcode hfork
      hrun hnp).cost + MachineState.memCost s.activeWords.toNat =
      copyStateWork + MachineState.memCost
        (copiesReturned s messageOffset returnDest rest).activeWords.toNat := by
  have hraw := Meter.runLocatedBlock_cost_potential copyStateLocated
    (run_copyState s messageOffset returnDest rest hstack hrun)
  have hcap (m : Nat) (hm : m ≤ 5) : rest.length + m < 1024 := by omega
  have hwork : Meter.runLocatedBlockCostWithoutMemory copyStateLocated
      (scheduleReturned s messageOffset returnDest rest) = copyStateWork := by
    simp [Meter.runLocatedBlockCostWithoutMemory, copyStateLocated,
      Stepper.runLocated, Stepper.runInstr, Meter.instrCostWithoutMemory,
      scheduleReturned, copyStateWork, Gas.baseCost, Gas.copyWordCost,
      hrun, hcap, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.add_assoc]
  rw [hwork] at hraw
  simpa [gasSteps_copyState, scheduleReturned] using hraw

def scheduleIterationWork : Nat :=
  Meter.runLocatedBlockStaticCost Schedule.conditionPath +
  Meter.runLocatedBlockStaticCost Schedule.setupReadPath +
  Meter.runLocatedBlockStaticCost Schedule.readLEPath +
  Meter.runLocatedBlockStaticCost Schedule.setupXSetPath +
  Meter.runLocatedBlockStaticCost Schedule.xSetPath +
  Meter.runLocatedBlockStaticCost Schedule.incrementPath

def scheduleWork : Nat :=
  Meter.runLocatedBlockStaticCost Schedule.scheduleStartPath +
  16 * scheduleIterationWork +
  Meter.runLocatedBlockStaticCost Schedule.conditionPath +
  Meter.runLocatedBlockStaticCost Schedule.exitPath

theorem scheduleIterationWork_eq : scheduleIterationWork = 230 := by
  rfl

theorem scheduleWork_eq : scheduleWork = 3722 := by rfl

theorem readLE_cost_potential (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Schedule.gasSteps_readLE s msgOff returnDest rest i hstack hcode hfork
      hrun hnp).cost + MachineState.memCost s.activeWords.toNat =
      Meter.runLocatedBlockStaticCost Schedule.readLEPath +
        MachineState.memCost
          (Schedule.afterRead s msgOff returnDest rest i).activeWords.toNat := by
  have hraw := blockCost_potential Schedule.readLEPath
    (Schedule.readEntry s msgOff returnDest rest i)
    (Schedule.afterRead s msgOff returnDest rest i)
    (Schedule.run_readLE s msgOff returnDest rest i hstack hcode hrun)
    (by simpa [Schedule.readEntry] using hfork)
    (by simp [Schedule.readLEPath, CopyFree])
  simpa [Schedule.gasSteps_readLE, Schedule.readEntry] using hraw

theorem scheduleIteration_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 16) (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Schedule.gasSteps_iteration_of_readLE s msgOff returnDest rest i hi hstack
      hcode hfork hrun hnp
      (Schedule.gasSteps_readLE s msgOff returnDest rest i hstack hcode hfork
        hrun hnp)).cost + MachineState.memCost s.activeWords.toNat =
      scheduleIterationWork + MachineState.memCost
        (Schedule.afterIteration s msgOff returnDest rest i).activeWords.toNat := by
  let q0 := Schedule.afterCondition s msgOff returnDest rest i
  let q1 := Schedule.readEntry s msgOff returnDest rest i
  let q2 := Schedule.afterRead s msgOff returnDest rest i
  let q3 := Schedule.xSetEntry s msgOff returnDest rest i
  let q4 := Schedule.afterStore s msgOff returnDest rest i
  let q5 := Schedule.afterIteration s msgOff returnDest rest i
  have h0 := blockCost_potential Schedule.conditionPath
    (Schedule.loopAt s msgOff returnDest rest i) q0
    (Schedule.run_condition_continue s msgOff returnDest rest i hi (by omega) hrun)
    (by simpa [Schedule.loopAt] using hfork)
    (by simp [Schedule.conditionPath, CopyFree])
  have h1 := blockCost_potential Schedule.setupReadPath q0 q1
    (Schedule.run_setupRead s msgOff returnDest rest i hi (by omega) hcode hrun)
    (by simpa [q0, Schedule.afterCondition, State.fork] using hfork)
    (by simp [Schedule.setupReadPath, CopyFree])
  have h2 := readLE_cost_potential s msgOff returnDest rest i hstack hcode
    hfork hrun hnp
  have h3 := blockCost_potential Schedule.setupXSetPath q2 q3
    (Schedule.run_setupXSet s msgOff returnDest rest i (by omega) hcode hrun)
    (by simpa [q2, Schedule.afterRead, State.fork] using hfork)
    (by simp [Schedule.setupXSetPath, CopyFree])
  have h4 := blockCost_potential Schedule.xSetPath q3 q4
    (Schedule.run_xSet s msgOff returnDest rest i hi (by omega) hcode hrun)
    (by simpa [q3, Schedule.xSetEntry, Schedule.afterRead, State.fork] using hfork)
    (by simp [Schedule.xSetPath, CopyFree])
  have h5 := blockCost_potential Schedule.incrementPath q4 q5
    (Schedule.run_increment s msgOff returnDest rest i hi (by omega) hcode hrun)
    (by simpa [q4, Schedule.afterStore, Schedule.afterRead, State.fork] using hfork)
    (by simp [Schedule.incrementPath, CopyFree])
  have h01 := potential_trans _ _ _ _ _ _ _ h0 h1
  have h012 := potential_trans _ _ _ _ _ _ _ h01 h2
  have h0123 := potential_trans _ _ _ _ _ _ _ h012 h3
  have h01234 := potential_trans _ _ _ _ _ _ _ h0123 h4
  have hall := potential_trans _ _ _ _ _ _ _ h01234 h5
  simpa [Schedule.gasSteps_iteration_of_readLE, Schedule.gasSteps_readLE,
    scheduleIterationWork, q0, q1, q2, q3, q4, q5, Schedule.loopAt,
    GasSteps.trans_cost, Nat.add_assoc] using hall

private def concreteScheduleRead (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (i : Nat) (_hi : i < 16) :
    GasSteps
      (Schedule.readEntry (Schedule.loopState s msgOff returnDest rest i)
        msgOff returnDest rest i)
      (Schedule.afterRead (Schedule.loopState s msgOff returnDest rest i)
        msgOff returnDest rest i) := by
  let q := Schedule.loopState s msgOff returnDest rest i
  apply Schedule.gasSteps_readLE q msgOff returnDest rest i hstack
  · simpa [q] using hcode
  · simpa [q, State.fork] using hfork
  · simpa [q] using hrun
  · simpa [q] using hnp

private def concreteScheduleIteration (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (i : Nat) (hi : i < 16) :
    GasSteps (Schedule.loopState s msgOff returnDest rest i)
      (Schedule.loopState s msgOff returnDest rest (i + 1)) := by
  let q := Schedule.loopState s msgOff returnDest rest i
  let gone := Schedule.gasSteps_iteration_of_readLE q msgOff returnDest rest
    i hi hstack (by simpa [q] using hcode)
    (by simpa [q, State.fork] using hfork) (by simpa [q] using hrun)
    (by simpa [q] using hnp)
    (by simpa [q] using
      (concreteScheduleRead s msgOff returnDest rest hstack hcode hfork hrun
        hnp i hi))
  exact GasSteps.cast gone (by simp [q]) (by simp [q, Schedule.loopState])

private theorem concreteScheduleIteration_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (i : Nat) (hi : i < 16) :
    (concreteScheduleIteration s msgOff returnDest rest hstack hcode hfork
      hrun hnp i hi).cost + MachineState.memCost
        (Schedule.loopState s msgOff returnDest rest i).activeWords.toNat =
      scheduleIterationWork + MachineState.memCost
        (Schedule.loopState s msgOff returnDest rest (i + 1)).activeWords.toNat := by
  have h := scheduleIteration_cost_potential
    (Schedule.loopState s msgOff returnDest rest i)
    msgOff returnDest rest i hi hstack
    (by simpa using hcode) (by simpa [State.fork] using hfork)
    (by simpa using hrun) (by simpa using hnp)
  calc
    _ = scheduleIterationWork + MachineState.memCost
          (Schedule.afterIteration
            (Schedule.loopState s msgOff returnDest rest i)
            msgOff returnDest rest i).activeWords.toNat := by
      simpa [concreteScheduleIteration, concreteScheduleRead] using h
    _ = scheduleIterationWork + MachineState.memCost
          (Schedule.loopState s msgOff returnDest rest (i + 1)).activeWords.toNat := by
      congr 2

private def concreteScheduleLoop (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps (Schedule.loopState s msgOff returnDest rest 0)
      (Schedule.loopState s msgOff returnDest rest 16) :=
  GasSteps.iterateBounded 16
    (concreteScheduleIteration s msgOff returnDest rest hstack hcode hfork
      hrun hnp)

theorem scheduleLoop_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (concreteScheduleLoop s msgOff returnDest rest hstack hcode hfork hrun
      hnp).cost + MachineState.memCost s.activeWords.toNat =
      16 * scheduleIterationWork + MachineState.memCost
        (Schedule.loopState s msgOff returnDest rest 16).activeWords.toNat := by
  unfold concreteScheduleLoop
  have hloop := Meter.iterateBounded_cost_potential_add 16
    scheduleIterationWork
    (concreteScheduleIteration s msgOff returnDest rest hstack hcode hfork
      hrun hnp)
    (concreteScheduleIteration_cost_potential s msgOff returnDest rest hstack
      hcode hfork hrun hnp)
  have hstart :
      (Schedule.loopState s msgOff returnDest rest 0).activeWords =
        s.activeWords := rfl
  rw [hstart] at hloop
  exact hloop

theorem combination_cost_potential (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (gasSteps_combination s messageOffset returnDest rest hstack hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      tailWork + MachineState.memCost
        (combinationReturned s messageOffset returnDest rest).activeWords.toNat := by
  let q0 := combination0 s messageOffset returnDest rest
  let q1 := combination1 s messageOffset returnDest rest
  let q2 := combination2 s messageOffset returnDest rest
  let q3 := combination3 s messageOffset returnDest rest
  let q4 := combination4 s messageOffset returnDest rest
  let qp := combinationCleaned s messageOffset returnDest rest
  let qr := combinationReturned s messageOffset returnDest rest
  have h0raw := blockCost_potential combination0Located
    (combinationEntry s messageOffset returnDest rest) q0
    (run_combination0 s messageOffset returnDest rest hstack hrun)
    (by simpa [combinationEntry] using hfork)
    (by simp [combination0Located, combinationLocated, CopyFree])
  have h0 : (gasSteps_combination0 s messageOffset returnDest rest hstack
      hcode hfork hrun hnp).cost + MachineState.memCost s.activeWords.toNat =
      Meter.runLocatedBlockStaticCost combination0Located +
        MachineState.memCost q0.activeWords.toNat := by
    simpa [gasSteps_combination0, q0, combinationEntry] using h0raw
  have h1raw := blockCost_potential combination1Located q0 q1
    (run_combination1 s messageOffset returnDest rest hstack hrun)
    (by simpa [q0, State.fork] using hfork)
    (by simp [combination1Located, combinationLocated, CopyFree])
  have h1 : (gasSteps_combination1 s messageOffset returnDest rest hstack
      hcode hfork hrun hnp).cost + MachineState.memCost q0.activeWords.toNat =
      Meter.runLocatedBlockStaticCost combination1Located +
        MachineState.memCost q1.activeWords.toNat := by
    simpa [gasSteps_combination1, q0, q1] using h1raw
  have h2raw := blockCost_potential combination2Located q1 q2
    (run_combination2 s messageOffset returnDest rest hstack hrun)
    (by simpa [q1, State.fork] using hfork)
    (by simp [combination2Located, combinationLocated, CopyFree])
  have h2 : (gasSteps_combination2 s messageOffset returnDest rest hstack
      hcode hfork hrun hnp).cost + MachineState.memCost q1.activeWords.toNat =
      Meter.runLocatedBlockStaticCost combination2Located +
        MachineState.memCost q2.activeWords.toNat := by
    simpa [gasSteps_combination2, q1, q2] using h2raw
  have h3raw := blockCost_potential combination3Located q2 q3
    (run_combination3 s messageOffset returnDest rest hstack hrun)
    (by simpa [q2, State.fork] using hfork)
    (by simp [combination3Located, combinationLocated, CopyFree])
  have h3 : (gasSteps_combination3 s messageOffset returnDest rest hstack
      hcode hfork hrun hnp).cost + MachineState.memCost q2.activeWords.toNat =
      Meter.runLocatedBlockStaticCost combination3Located +
        MachineState.memCost q3.activeWords.toNat := by
    simpa [gasSteps_combination3, q2, q3] using h3raw
  have h4raw := blockCost_potential combination4Located q3 q4
    (run_combination4 s messageOffset returnDest rest hstack hrun)
    (by simpa [q3, State.fork] using hfork)
    (by simp [combination4Located, combinationLocated, CopyFree])
  have h4 : (gasSteps_combination4 s messageOffset returnDest rest hstack
      hcode hfork hrun hnp).cost + MachineState.memCost q3.activeWords.toNat =
      Meter.runLocatedBlockStaticCost combination4Located +
        MachineState.memCost q4.activeWords.toNat := by
    simpa [gasSteps_combination4, q3, q4] using h4raw
  have hpraw := blockCost_potential combinationPopsLocated q4 qp
    (run_combinationPops s messageOffset returnDest rest hstack hrun)
    (by simpa [q4, State.fork] using hfork)
    (by simp [combinationPopsLocated, combinationCleanupLocated,
      combinationLocated, CopyFree])
  have hp : (gasSteps_combinationPops s messageOffset returnDest rest hstack
      hcode hfork hrun hnp).cost + MachineState.memCost q4.activeWords.toNat =
      Meter.runLocatedBlockStaticCost combinationPopsLocated +
        MachineState.memCost qp.activeWords.toNat := by
    simpa [gasSteps_combinationPops, q4, qp] using hpraw
  have hjraw := blockCost_potential combinationJumpLocated qp qr
    (run_combinationJump s messageOffset returnDest rest hstack hcode hrun hvalid)
    (by simpa [qp, State.fork] using hfork)
    (by simp [combinationJumpLocated, combinationCleanupLocated,
      combinationLocated, CopyFree])
  have hj : (gasSteps_combinationJump s messageOffset returnDest rest hstack
      hcode hfork hrun hnp hvalid).cost +
        MachineState.memCost qp.activeWords.toNat =
      Meter.runLocatedBlockStaticCost combinationJumpLocated +
        MachineState.memCost qr.activeWords.toNat := by
    simpa [gasSteps_combinationJump, qp, qr] using hjraw
  have h01 := potential_trans _ _ _ _ _ _ _ h0 h1
  have h012 := potential_trans _ _ _ _ _ _ _ h01 h2
  have h0123 := potential_trans _ _ _ _ _ _ _ h012 h3
  have h01234 := potential_trans _ _ _ _ _ _ _ h0123 h4
  have h01234p := potential_trans _ _ _ _ _ _ _ h01234 hp
  have hall := potential_trans _ _ _ _ _ _ _ h01234p hj
  simpa [gasSteps_combination, tailWork, q0, q1, q2, q3, q4, qp, qr,
    GasSteps.trans_cost, Nat.add_assoc] using hall

end Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionCostTrace
