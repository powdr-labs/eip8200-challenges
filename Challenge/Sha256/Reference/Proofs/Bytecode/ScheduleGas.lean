import Challenge.EvmProof.Meter
import Challenge.Sha256.Reference.Proofs.Bytecode.ArithmeticGas
import Challenge.Sha256.Reference.Proofs.Bytecode.Schedule

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Challenge.Sha256.Reference.Proofs.Bytecode.ScheduleGas

open Challenge.Sha256
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Sha256.Reference.Proofs.Bytecode

private def CopyFree : Instr → Prop
  | .op .CALLDATACOPY => False
  | .op .MCOPY => False
  | _ => True

private theorem noMemoryCost_eq_static (instruction : Instr) (s : State)
    (fork : Fork) (hfork : s.fork = fork) (hfree : CopyFree instruction) :
    Challenge.EvmProof.Meter.instrCostWithoutMemory instruction s =
      Challenge.EvmProof.Meter.instrStaticCost fork instruction := by
  cases instruction with
  | push width value =>
      simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
        Challenge.EvmProof.Meter.instrStaticCost, hfork]
  | op op =>
      cases op with
      | StopArith op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | CompBit op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Keccak op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Env op => cases op <;> simp [CopyFree,
          Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork] at hfree ⊢
      | Block op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | StackMemFlow op => cases op <;> simp [CopyFree,
          Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork] at hfree ⊢
      | Push op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Dup op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Swap op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | DupN op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | SwapN op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Exchange op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Log op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | System op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]

private theorem blockCost_potential_of_static
    {artifact : Challenge.EvmProof.ProgramArtifact} {fork : Fork}
    (path : List (Challenge.EvmProof.Stepper.Located artifact fork)) {s t : State}
    (work : Nat)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = fork)
    (hfree : ∀ located ∈ path, CopyFree located.instruction)
    (hcost : Challenge.EvmProof.Meter.runLocatedBlockStaticCost path = work) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path s +
        MachineState.memCost s.activeWords.toNat =
      work + MachineState.memCost t.activeWords.toNat := by
  rw [Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential path
    hresult hfork]
  · simp [hcost]
  · intro located hmem q hq
    exact noMemoryCost_eq_static located.instruction q fork hq
      (hfree located hmem)

private theorem wAt_cost_potential (s : State)
    (index output returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1018)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (Accessors.gasSteps_wAt s index output returnDest rest hcap hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      37 + MachineState.memCost
        (Accessors.loadReturned s 800 index returnDest rest).activeWords.toNat := by
  have hresult := Accessors.run_load Accessors.wAtPath s 279 800
    index output returnDest rest (Or.inl ⟨rfl, rfl, rfl⟩) hcap hcode hrun hvalid
  have hmeter := blockCost_potential_of_static Accessors.wAtPath 37 hresult hfork
    (by simp [Accessors.wAtPath, CopyFree]) (by rfl)
  unfold Accessors.gasSteps_wAt
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  exact hmeter

private theorem wSet_cost_potential (s : State)
    (index value returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (Accessors.gasSteps_wSet s index value returnDest rest hcap hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      34 + MachineState.memCost
        (Accessors.storeReturned s 800 index value returnDest rest).activeWords.toNat := by
  have hresult := Accessors.run_store Accessors.wSetPath s 299 800
    index value returnDest rest (Or.inl ⟨rfl, rfl, rfl⟩) hcap hcode hrun hvalid
  have hmeter := blockCost_potential_of_static Accessors.wSetPath 34 hresult hfork
    (by simp [Accessors.wSetPath, CopyFree]) (by rfl)
  unfold Accessors.gasSteps_wSet
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  exact hmeter

theorem firstIteration_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat)
    (hj : j < 16) (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Schedule.gasSteps_firstIteration s msgOff returnDest rest j hj hstack
      hcode hfork hrun hnp).cost +
        MachineState.memCost (Schedule.firstAt s msgOff returnDest rest j).activeWords.toNat =
      103 + MachineState.memCost
        (Schedule.afterFirstIteration s msgOff returnDest rest j).activeWords.toNat := by
  have hcond := blockCost_potential_of_static Schedule.firstConditionPath 26
    (Schedule.run_firstCondition s msgOff returnDest rest j hj (by omega) hrun)
    (by simpa [Schedule.firstAt, State.fork] using hfork)
    (by simp [Schedule.firstConditionPath, CopyFree]) (by rfl)
  have hload := blockCost_potential_of_static Schedule.firstLoadPath 24
    (Schedule.run_firstLoad s msgOff returnDest rest j (by omega) hrun)
    (by simpa [Schedule.afterFirstCondition, Schedule.firstAt, State.fork]
      using hfork)
    (by simp [Schedule.firstLoadPath, CopyFree]) (by rfl)
  have hstore := blockCost_potential_of_static Schedule.firstStorePath 28
    (Schedule.run_firstStore s msgOff returnDest rest j hstack hrun)
    (by simpa [Schedule.afterFirstLoad, Schedule.afterFirstCondition,
      Schedule.firstAt, State.fork] using hfork)
    (by simp [Schedule.firstStorePath, CopyFree]) (by rfl)
  have hinc := blockCost_potential_of_static Schedule.firstIncrementPath 25
    (Schedule.run_firstIncrement s msgOff returnDest rest j hj (by omega)
      hcode hrun)
    (by simpa [Schedule.afterFirstStore, Schedule.afterFirstLoad,
      Schedule.afterFirstCondition, Schedule.firstAt, State.fork] using hfork)
    (by simp [Schedule.firstIncrementPath, CopyFree]) (by rfl)
  simp only [Schedule.gasSteps_firstIteration,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

theorem firstLoop_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Schedule.gasSteps_firstLoop s msgOff returnDest rest hstack hcode hfork
      hrun hnp).cost + MachineState.memCost
        (Schedule.firstLoopState s msgOff returnDest rest 0).activeWords.toNat =
      16 * 103 + MachineState.memCost
        (Schedule.firstLoopState s msgOff returnDest rest 16).activeWords.toNat := by
  unfold Schedule.gasSteps_firstLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add 16 103
  intro i hi
  let q := Schedule.firstLoopState s msgOff returnDest rest i
  have qcode : q.executionEnv.code = referenceBytecode := by simpa [q] using hcode
  have qfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have qrun : q.halt = .Running := by simpa [q] using hrun
  have qnp : Precompile.isPrecompile q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  have h := firstIteration_cost_potential q msgOff returnDest rest i hi hstack
    qcode qfork qrun qnp
  dsimp only [q] at h
  have h' :
      (Schedule.gasSteps_firstIteration
        (Schedule.firstLoopState s msgOff returnDest rest i)
        msgOff returnDest rest i hi hstack qcode qfork qrun qnp).cost +
          MachineState.memCost
            (Schedule.firstLoopState s msgOff returnDest rest i).activeWords.toNat =
        103 + MachineState.memCost
          (Schedule.firstLoopState s msgOff returnDest rest (i + 1)).activeWords.toNat := by
    simpa [Schedule.firstAt, Schedule.firstLoopState] using h
  simpa only [Challenge.EvmProof.GasSteps.cast_cost] using h'

theorem secondIteration_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat)
    (hj16 : 16 ≤ j) (hj64 : j < 64) (hstack : rest.length < 990)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Schedule.gasSteps_secondIteration s msgOff returnDest rest j hj16 hj64
      hstack hcode hfork hrun hnp).cost + MachineState.memCost
        (Schedule.secondAt s msgOff returnDest rest j).activeWords.toNat =
      780 + MachineState.memCost
        (Schedule.afterSecondIteration s msgOff returnDest rest j).activeWords.toNat := by
  have hcond := blockCost_potential_of_static Schedule.secondConditionPath 26
    (Schedule.run_secondCondition s msgOff returnDest rest j hj16 hj64
      (by omega) hrun)
    (by simpa [Schedule.secondAt, State.fork] using hfork)
    (by simp [Schedule.secondConditionPath, CopyFree]) (by rfl)
  have hW16 := blockCost_potential_of_static Schedule.setupW16Path 31
    (Schedule.run_setupW16 s msgOff returnDest rest j hj16 hj64 (by omega)
      hcode hrun)
    (by simpa [Schedule.afterSecondCondition, Schedule.secondAt, State.fork]
      using hfork)
    (by simp [Schedule.setupW16Path, CopyFree]) (by rfl)
  have hcall16 := wAt_cost_potential s (UInt256.ofNat (j - 16)) 0
    (UInt256.ofNat 525)
    ([UInt256.ofNat 0xffffffff, UInt256.ofNat 592, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)
    (by simp; omega) hcode hfork hrun hnp (by decide)
  let q16 := Schedule.gotW16 s msgOff returnDest rest j
  have q16code : q16.executionEnv.code = referenceBytecode := by
    simpa [q16, Schedule.gotW16, Accessors.loadReturned] using hcode
  have q16fork : q16.fork = .Osaka := by
    simpa [q16, Schedule.gotW16, Accessors.loadReturned, State.fork] using hfork
  have q16run : q16.halt = .Running := by
    simpa [q16, Schedule.gotW16, Accessors.loadReturned] using hrun
  have q16np : Precompile.isPrecompile q16.executionEnv.fork
      q16.executionEnv.codeAddr = false := by
    simpa [q16, Schedule.gotW16, Accessors.loadReturned] using hnp
  have hW15 := blockCost_potential_of_static Schedule.setupW15Path 31
    (Schedule.run_setupW15 s msgOff returnDest rest j hj16 hj64 (by omega)
      hcode hrun) q16fork
    (by simp [Schedule.setupW15Path, CopyFree]) (by rfl)
  have hcall15 := wAt_cost_potential q16 (UInt256.ofNat (j - 15)) 0
    (UInt256.ofNat 542)
    ([0, UInt256.ofNat 547, Schedule.wValue s (j - 16),
      UInt256.ofNat 0xffffffff, UInt256.ofNat 592, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)
    (by simp; omega) q16code q16fork q16run q16np (by decide)
  let q15 := Schedule.gotW15 s msgOff returnDest rest j
  have q15code : q15.executionEnv.code = referenceBytecode := by
    simpa [q15, Schedule.gotW15, q16, Accessors.loadReturned] using q16code
  have q15fork : q15.fork = .Osaka := by
    simpa [q15, Schedule.gotW15, q16, Accessors.loadReturned, State.fork]
      using q16fork
  have q15run : q15.halt = .Running := by
    simpa [q15, Schedule.gotW15, q16, Accessors.loadReturned] using q16run
  have q15np : Precompile.isPrecompile q15.executionEnv.fork
      q15.executionEnv.codeAddr = false := by
    simpa [q15, Schedule.gotW15, q16, Accessors.loadReturned] using q16np
  have hsetupS0 := blockCost_potential_of_static Schedule.setupSsig0Path 12
    (Schedule.run_setupSsig0 s msgOff returnDest rest j (by omega) hcode hrun)
    q15fork (by simp [Schedule.setupSsig0Path, CopyFree]) (by rfl)
  have hcallS0 := ArithmeticGas.gasSteps_ssig0_cost_potential q15
    (Schedule.wValue q15 (j - 15)) 0 (UInt256.ofNat 547)
    ([Schedule.wValue s (j - 16), UInt256.ofNat 0xffffffff,
      UInt256.ofNat 592, UInt256.ofNat j, msgOff, returnDest] ++ rest)
    (by simp; omega) q15code q15fork q15run q15np (by decide)
  let qs0 := Schedule.gotSsig0 s msgOff returnDest rest j
  have qs0code : qs0.executionEnv.code = referenceBytecode := by
    simpa [qs0, Schedule.gotSsig0, q15, Functions.unaryReturned] using q15code
  have qs0fork : qs0.fork = .Osaka := by
    simpa [qs0, Schedule.gotSsig0, q15, Functions.unaryReturned, State.fork]
      using q15fork
  have qs0run : qs0.halt = .Running := by
    simpa [qs0, Schedule.gotSsig0, q15, Functions.unaryReturned] using q15run
  have qs0np : Precompile.isPrecompile qs0.executionEnv.fork
      qs0.executionEnv.codeAddr = false := by
    simpa [qs0, Schedule.gotSsig0, q15, Functions.unaryReturned] using q15np
  have hW7 := blockCost_potential_of_static Schedule.setupW7Path 29
    (Schedule.run_setupW7 s msgOff returnDest rest j hj16 hj64 (by omega)
      hcode hrun) qs0fork
    (by simp [Schedule.setupW7Path, CopyFree]) (by rfl)
  have hcall7 := wAt_cost_potential qs0 (UInt256.ofNat (j - 7)) 0
    (UInt256.ofNat 561)
    ([Schedule.firstSum s msgOff returnDest rest j, UInt256.ofNat 0xffffffff,
      UInt256.ofNat 592, UInt256.ofNat j, msgOff, returnDest] ++ rest)
    (by simp; omega) qs0code qs0fork qs0run qs0np (by decide)
  let q7 := Schedule.gotW7 s msgOff returnDest rest j
  have q7code : q7.executionEnv.code = referenceBytecode := by
    simpa [q7, Schedule.gotW7, qs0, Accessors.loadReturned] using qs0code
  have q7fork : q7.fork = .Osaka := by
    simpa [q7, Schedule.gotW7, qs0, Accessors.loadReturned, State.fork]
      using qs0fork
  have q7run : q7.halt = .Running := by
    simpa [q7, Schedule.gotW7, qs0, Accessors.loadReturned] using qs0run
  have q7np : Precompile.isPrecompile q7.executionEnv.fork
      q7.executionEnv.codeAddr = false := by
    simpa [q7, Schedule.gotW7, qs0, Accessors.loadReturned] using qs0np
  have hW2 := blockCost_potential_of_static Schedule.setupW2Path 31
    (Schedule.run_setupW2 s msgOff returnDest rest j hj16 hj64 (by omega)
      hcode hrun) q7fork
    (by simp [Schedule.setupW2Path, CopyFree]) (by rfl)
  have hcall2 := wAt_cost_potential q7 (UInt256.ofNat (j - 2)) 0
    (UInt256.ofNat 578)
    ([0, UInt256.ofNat 583, Schedule.wValue q7 (j - 7),
      Schedule.firstSum s msgOff returnDest rest j, UInt256.ofNat 0xffffffff,
      UInt256.ofNat 592, UInt256.ofNat j, msgOff, returnDest] ++ rest)
    (by simp; omega) q7code q7fork q7run q7np (by decide)
  let q2 := Schedule.gotW2 s msgOff returnDest rest j
  have q2code : q2.executionEnv.code = referenceBytecode := by
    simpa [q2, Schedule.gotW2, q7, Accessors.loadReturned] using q7code
  have q2fork : q2.fork = .Osaka := by
    simpa [q2, Schedule.gotW2, q7, Accessors.loadReturned, State.fork]
      using q7fork
  have q2run : q2.halt = .Running := by
    simpa [q2, Schedule.gotW2, q7, Accessors.loadReturned] using q7run
  have q2np : Precompile.isPrecompile q2.executionEnv.fork
      q2.executionEnv.codeAddr = false := by
    simpa [q2, Schedule.gotW2, q7, Accessors.loadReturned] using q7np
  have hsetupS1 := blockCost_potential_of_static Schedule.setupSsig1Path 12
    (Schedule.run_setupSsig1 s msgOff returnDest rest j (by omega) hcode hrun)
    q2fork (by simp [Schedule.setupSsig1Path, CopyFree]) (by rfl)
  have hcallS1 := ArithmeticGas.gasSteps_ssig1_cost_potential q2
    (Schedule.wValue q2 (j - 2)) 0 (UInt256.ofNat 583)
    ([Schedule.wValue q7 (j - 7),
      Schedule.firstSum s msgOff returnDest rest j, UInt256.ofNat 0xffffffff,
      UInt256.ofNat 592, UInt256.ofNat j, msgOff, returnDest] ++ rest)
    (by simp; omega) q2code q2fork q2run q2np (by decide)
  let qs1 := Schedule.gotSsig1 s msgOff returnDest rest j
  have qs1code : qs1.executionEnv.code = referenceBytecode := by
    simpa [qs1, Schedule.gotSsig1, q2, Functions.unaryReturned] using q2code
  have qs1fork : qs1.fork = .Osaka := by
    simpa [qs1, Schedule.gotSsig1, q2, Functions.unaryReturned, State.fork]
      using q2fork
  have qs1run : qs1.halt = .Running := by
    simpa [qs1, Schedule.gotSsig1, q2, Functions.unaryReturned] using q2run
  have qs1np : Precompile.isPrecompile qs1.executionEnv.fork
      qs1.executionEnv.codeAddr = false := by
    simpa [qs1, Schedule.gotSsig1, q2, Functions.unaryReturned] using q2np
  have hfinish := blockCost_potential_of_static Schedule.finishRecurrencePath 24
    (Schedule.run_finishRecurrence s msgOff returnDest rest j (by omega)
      hcode hrun) qs1fork
    (by simp [Schedule.finishRecurrencePath, CopyFree]) (by rfl)
  have hset := wSet_cost_potential qs1 (UInt256.ofNat j)
    (Schedule.recurrenceWord s msgOff returnDest rest j) (UInt256.ofNat 592)
    ([UInt256.ofNat j, msgOff, returnDest] ++ rest)
    (by simp; omega) qs1code qs1fork qs1run qs1np (by decide)
  let qset := Schedule.gotWSet s msgOff returnDest rest j
  have qsetfork : qset.fork = .Osaka := by
    simpa [qset, Schedule.gotWSet, qs1, Accessors.storeReturned, State.fork]
      using qs1fork
  have hinc := blockCost_potential_of_static Schedule.secondIncrementPath 26
    (Schedule.run_secondIncrement s msgOff returnDest rest j hj64 (by omega)
      hcode hrun) qsetfork
    (by simp [Schedule.secondIncrementPath, CopyFree]) (by rfl)
  dsimp only [q16] at hcall15
  dsimp only [q15] at hcall15 hcallS0
  dsimp only [qs0] at hcallS0 hcall7
  dsimp only [q7] at hcall7 hcall2 hcallS1
  dsimp only [q2] at hcall2 hcallS1
  dsimp only [qs1] at hcallS1 hset
  simp only [Accessors.gasSteps_wAt, Accessors.gasSteps_wSet,
    Functions.gasSteps_ssig0, Functions.gasSteps_ssig1,
    Functions.gasSteps_rotr, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
    at hcall16 hcall15 hcallS0 hcall7 hcall2 hcallS1 hset
  change _ + MachineState.memCost s.activeWords.toNat =
    26 + MachineState.memCost s.activeWords.toNat at hcond
  change _ + MachineState.memCost s.activeWords.toNat =
    31 + MachineState.memCost s.activeWords.toNat at hW16
  change _ + MachineState.memCost s.activeWords.toNat =
    37 + MachineState.memCost
      (Schedule.gotW16 s msgOff returnDest rest j).activeWords.toNat at hcall16
  change _ + MachineState.memCost
      (Schedule.gotW16 s msgOff returnDest rest j).activeWords.toNat =
    31 + MachineState.memCost
      (Schedule.gotW16 s msgOff returnDest rest j).activeWords.toNat at hW15
  change _ + MachineState.memCost
      (Schedule.gotW16 s msgOff returnDest rest j).activeWords.toNat =
    37 + MachineState.memCost
      (Schedule.gotW15 s msgOff returnDest rest j).activeWords.toNat at hcall15
  change _ + MachineState.memCost
      (Schedule.gotW15 s msgOff returnDest rest j).activeWords.toNat =
    12 + MachineState.memCost
      (Schedule.gotW15 s msgOff returnDest rest j).activeWords.toNat at hsetupS0
  change _ + MachineState.memCost
      (Schedule.gotW15 s msgOff returnDest rest j).activeWords.toNat =
    188 + MachineState.memCost
      (Schedule.gotW15 s msgOff returnDest rest j).activeWords.toNat at hcallS0
  change _ + MachineState.memCost
      (Schedule.gotW15 s msgOff returnDest rest j).activeWords.toNat =
    29 + MachineState.memCost
      (Schedule.gotW15 s msgOff returnDest rest j).activeWords.toNat at hW7
  change _ + MachineState.memCost
      (Schedule.gotW15 s msgOff returnDest rest j).activeWords.toNat =
    37 + MachineState.memCost
      (Schedule.gotW7 s msgOff returnDest rest j).activeWords.toNat at hcall7
  change _ + MachineState.memCost
      (Schedule.gotW7 s msgOff returnDest rest j).activeWords.toNat =
    31 + MachineState.memCost
      (Schedule.gotW7 s msgOff returnDest rest j).activeWords.toNat at hW2
  change _ + MachineState.memCost
      (Schedule.gotW7 s msgOff returnDest rest j).activeWords.toNat =
    37 + MachineState.memCost
      (Schedule.gotW2 s msgOff returnDest rest j).activeWords.toNat at hcall2
  change _ + MachineState.memCost
      (Schedule.gotW2 s msgOff returnDest rest j).activeWords.toNat =
    12 + MachineState.memCost
      (Schedule.gotW2 s msgOff returnDest rest j).activeWords.toNat at hsetupS1
  change _ + MachineState.memCost
      (Schedule.gotW2 s msgOff returnDest rest j).activeWords.toNat =
    188 + MachineState.memCost
      (Schedule.gotW2 s msgOff returnDest rest j).activeWords.toNat at hcallS1
  change _ + MachineState.memCost
      (Schedule.gotW2 s msgOff returnDest rest j).activeWords.toNat =
    24 + MachineState.memCost
      (Schedule.gotW2 s msgOff returnDest rest j).activeWords.toNat at hfinish
  change _ + MachineState.memCost
      (Schedule.gotW2 s msgOff returnDest rest j).activeWords.toNat =
    34 + MachineState.memCost
      (Schedule.gotWSet s msgOff returnDest rest j).activeWords.toNat at hset
  change _ + MachineState.memCost
      (Schedule.gotWSet s msgOff returnDest rest j).activeWords.toNat =
    26 + MachineState.memCost
      (Schedule.gotWSet s msgOff returnDest rest j).activeWords.toNat at hinc
  simp only [Schedule.gasSteps_secondIteration,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost,
    Accessors.gasSteps_wAt, Accessors.gasSteps_wSet,
    Functions.gasSteps_ssig0, Functions.gasSteps_ssig1,
    Functions.gasSteps_rotr]
  change _ + MachineState.memCost s.activeWords.toNat =
    780 + MachineState.memCost
      (Schedule.gotWSet s msgOff returnDest rest j).activeWords.toNat
  omega

theorem secondLoop_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 990)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Schedule.gasSteps_secondLoop s msgOff returnDest rest hstack hcode hfork
      hrun hnp).cost + MachineState.memCost
        (Schedule.secondLoopState s msgOff returnDest rest 0).activeWords.toNat =
      48 * 780 + MachineState.memCost
        (Schedule.secondLoopState s msgOff returnDest rest 48).activeWords.toNat := by
  unfold Schedule.gasSteps_secondLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add 48 780
  intro n hn
  let q := Schedule.secondLoopState s msgOff returnDest rest n
  have qcode : q.executionEnv.code = referenceBytecode := by simpa [q] using hcode
  have qfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have qrun : q.halt = .Running := by simpa [q] using hrun
  have qnp : Precompile.isPrecompile q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  have h := secondIteration_cost_potential q msgOff returnDest rest (16 + n)
    (by omega) (by omega) hstack qcode qfork qrun qnp
  dsimp only [q] at h
  have h' :
      (Schedule.gasSteps_secondIteration
        (Schedule.secondLoopState s msgOff returnDest rest n)
        msgOff returnDest rest (16 + n) (by omega) (by omega) hstack
        qcode qfork qrun qnp).cost + MachineState.memCost
          (Schedule.secondLoopState s msgOff returnDest rest n).activeWords.toNat =
        780 + MachineState.memCost
          (Schedule.secondLoopState s msgOff returnDest rest (n + 1)).activeWords.toNat := by
    simpa [Schedule.secondAt, Schedule.secondLoopState] using h
  simpa only [Challenge.EvmProof.GasSteps.cast_cost] using h'

theorem scheduleStart_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1021)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Schedule.gasSteps_scheduleStart s msgOff returnDest rest hstack hcode hfork
      hrun hnp).cost + MachineState.memCost
        (Schedule.scheduleEntry s msgOff returnDest rest).activeWords.toNat =
      3 + MachineState.memCost
        (Schedule.firstLoopState s msgOff returnDest rest 0).activeWords.toNat := by
  have h := blockCost_potential_of_static Schedule.scheduleStartPath 3
    (Schedule.run_scheduleStart s msgOff returnDest rest hstack hrun)
    (by simpa [Schedule.scheduleEntry, State.fork] using hfork)
    (by simp [Schedule.scheduleStartPath, CopyFree]) (by rfl)
  unfold Schedule.gasSteps_scheduleStart
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  exact h

theorem firstExit_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Schedule.gasSteps_firstExit s msgOff returnDest rest hstack hcode hfork
      hrun hnp).cost + MachineState.memCost
        (Schedule.firstAt s msgOff returnDest rest 16).activeWords.toNat =
      32 + MachineState.memCost
        (Schedule.secondAt s msgOff returnDest rest 16).activeWords.toNat := by
  have h := blockCost_potential_of_static Schedule.firstExitPath 32
    (Schedule.run_firstExit s msgOff returnDest rest hstack hcode hrun)
    (by simpa [Schedule.firstAt, State.fork] using hfork)
    (by simp [Schedule.firstExitPath, Schedule.firstConditionPath, CopyFree])
    (by rfl)
  unfold Schedule.gasSteps_firstExit
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  exact h

theorem secondExit_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (Schedule.gasSteps_secondExit s msgOff returnDest rest hstack hcode hfork
      hrun hnp hreturn).cost + MachineState.memCost
        (Schedule.secondAt s msgOff returnDest rest 64).activeWords.toNat =
      39 + MachineState.memCost
        (Schedule.scheduleReturned s returnDest rest).activeWords.toNat := by
  have h := blockCost_potential_of_static Schedule.secondExitPath 39
    (Schedule.run_secondExit s msgOff returnDest rest hstack hcode hrun hreturn)
    (by simpa [Schedule.secondAt, State.fork] using hfork)
    (by simp [Schedule.secondExitPath, Schedule.secondConditionPath, CopyFree])
    (by rfl)
  unfold Schedule.gasSteps_secondExit
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  exact h

theorem schedule_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 990)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Schedule.gasSteps_scheduleCost s msgOff returnDest rest hstack hcode hfork
      hrun hnp hreturn + MachineState.memCost
        (Schedule.scheduleEntry s msgOff returnDest rest).activeWords.toNat =
      39162 + MachineState.memCost
        (Schedule.scheduleResult s msgOff returnDest rest).activeWords.toNat := by
  let q1 := Schedule.firstLoopState s msgOff returnDest rest 16
  let q2 := Schedule.secondLoopState q1 msgOff returnDest rest 48
  have hstart := scheduleStart_cost_potential s msgOff returnDest rest (by omega)
    hcode hfork hrun hnp
  have hfirst := firstLoop_cost_potential s msgOff returnDest rest (by omega)
    hcode hfork hrun hnp
  have q1code : q1.executionEnv.code = referenceBytecode := by simpa [q1] using hcode
  have q1fork : q1.fork = .Osaka := by simpa [q1, State.fork] using hfork
  have q1run : q1.halt = .Running := by simpa [q1] using hrun
  have q1np : Precompile.isPrecompile q1.executionEnv.fork
      q1.executionEnv.codeAddr = false := by simpa [q1] using hnp
  have hbridge := firstExit_cost_potential q1 msgOff returnDest rest (by omega)
    q1code q1fork q1run q1np
  have hsecond := secondLoop_cost_potential q1 msgOff returnDest rest hstack
    q1code q1fork q1run q1np
  have q2code : q2.executionEnv.code = referenceBytecode := by simpa [q2] using q1code
  have q2fork : q2.fork = .Osaka := by simpa [q2, State.fork] using q1fork
  have q2run : q2.halt = .Running := by simpa [q2] using q1run
  have q2np : Precompile.isPrecompile q2.executionEnv.fork
      q2.executionEnv.codeAddr = false := by simpa [q2] using q1np
  have hfinish := secondExit_cost_potential q2 msgOff returnDest rest (by omega)
    q2code q2fork q2run q2np hreturn
  simp only [Schedule.gasSteps_scheduleCost, Schedule.gasSteps_schedule,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.GasSteps.cast_cost]
  dsimp only [q1] at hbridge hsecond
  dsimp only [q2, q1] at hfinish
  change _ + MachineState.memCost
      (Schedule.scheduleEntry s msgOff returnDest rest).activeWords.toNat =
    3 + MachineState.memCost
      (Schedule.scheduleEntry s msgOff returnDest rest).activeWords.toNat at hstart
  change _ + MachineState.memCost
      (Schedule.scheduleEntry s msgOff returnDest rest).activeWords.toNat =
    16 * 103 + MachineState.memCost q1.activeWords.toNat at hfirst
  change _ + MachineState.memCost q1.activeWords.toNat =
    32 + MachineState.memCost q1.activeWords.toNat at hbridge
  change _ + MachineState.memCost q1.activeWords.toNat =
    48 * 780 + MachineState.memCost q2.activeWords.toNat at hsecond
  change _ + MachineState.memCost q2.activeWords.toNat =
    39 + MachineState.memCost q2.activeWords.toNat at hfinish
  dsimp [Schedule.scheduleResult]
  change _ + MachineState.memCost
      (Schedule.scheduleEntry s msgOff returnDest rest).activeWords.toNat =
    39162 + MachineState.memCost q2.activeWords.toNat
  omega

end Challenge.Sha256.Reference.Proofs.Bytecode.ScheduleGas
