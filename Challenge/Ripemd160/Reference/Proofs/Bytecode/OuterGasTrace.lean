import Challenge.Ripemd160.Reference.Proofs.Bytecode.ExactGasBridge
import Challenge.Ripemd160.Reference.Proofs.Bytecode.OutputResultBridge
import Challenge.Ripemd160.Reference.Proofs.Bytecode.PaddingGasTrace
import Batteries.Tactic.OpenPrivate

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.OuterGasTrace

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM

open private gasSteps_driver gasSteps_output gasSteps_outputLoop
  gasSteps_outputIteration gasSteps_writeWord gasSteps_writeLoop
  gasSteps_writeIteration loadedH writeLoopState afterWrittenWord
  outputLoopState outputResult writeLoopState_normalized
  outputLoopState_normalized from
  Challenge.Ripemd160.Reference.Proofs.Bytecode.DirectCorrect

open private gasSteps_padPrefix run_lengthCondition run_lengthByte
  run_lengthStore run_lengthIncrement run_lengthBackPush run_lengthBackJump
  lengthBackReturned_eq run_lengthCopy run_lengthSentinelAddress
  run_lengthSentinelStore run_lengthFooterSetup padSentinelStored_eq
  run_enter run_paddedLength run_lengthExitCompare run_lengthExitZero
  run_lengthExitDest run_lengthExitJumpToBody run_lengthExitPop
  run_lengthExitSwap run_lengthExitJump padReturnedFromExit_eq from
  Challenge.Ripemd160.Reference.Proofs.Bytecode.PaddingTrace

private theorem block_cost_potential (path : List Output.Located)
    (s t : State) (work : Nat)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hstatic : ∀ located, located ∈ path → ∀ q, q.fork = .Osaka →
      Challenge.EvmProof.Meter.instrCostWithoutMemory located.instruction q =
        Challenge.EvmProof.Meter.instrStaticCost .Osaka located.instruction)
    (hwork : Challenge.EvmProof.Meter.runLocatedBlockStaticCost path = work) :
    (Output.gasSteps_block path s t hcode hfork hresult hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      work + MachineState.memCost t.activeWords.toNat := by
  rw [Output.gasSteps_block_cost]
  rw [Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential path
    hresult hfork hstatic, hwork]

set_option linter.unusedSimpArgs false in
private theorem writeIteration_cost_potential (s : State) (offset : Nat)
    (word ret : UInt256) (tail : List UInt256) (j : Nat) (hj : j < 4)
    (htail : tail.length < 1016) (hoff : offset + 3 < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_writeIteration s offset word ret tail j hj htail hoff hcode
      hfork hrun hnp).cost +
        MachineState.memCost
          (writeLoopState s offset word ret tail j).activeWords.toNat =
      84 + MachineState.memCost
        (writeLoopState s offset word ret tail (j + 1)).activeWords.toNat := by
  let q := writeLoopState s offset word ret tail j
  have qcode : q.executionEnv.code = referenceBytecode := by simpa [q] using hcode
  have qfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have qrun : q.halt = .Running := by simpa [q] using hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  let testStart : State := { q with
    pc := UInt256.ofNat 0x3c8
    stack := UInt256.ofNat j :: UInt256.ofNat offset :: word :: ret :: tail }
  let testEnd : State := { q with
    pc := UInt256.ofNat 0x3d2
    stack := UInt256.ofNat j :: UInt256.ofNat offset :: word :: ret :: tail }
  have htestRun : Challenge.EvmProof.Stepper.runLocatedBlock
      OutputTrace.writeTestPath testStart = some testEnd := by
    simpa [testStart, testEnd] using OutputTrace.run_writeTest_continue q j
      (UInt256.ofNat offset :: word :: ret :: tail) hj (by simp; omega) qrun
  let gtestRaw := Output.gasSteps_block OutputTrace.writeTestPath testStart testEnd
    qcode qfork htestRun qrun qnp
  let gtest : GasSteps q testEnd := GasSteps.cast gtestRaw
    (by simpa [q, testStart] using
      writeLoopState_normalized s offset word ret tail j) rfl
  have htest : gtest.cost + MachineState.memCost q.activeWords.toNat =
      26 + MachineState.memCost testEnd.activeWords.toNat := by
    have hraw := block_cost_potential OutputTrace.writeTestPath testStart testEnd
      26 qcode qfork htestRun qrun qnp
      (by
        intro located hmem z hz
        simp [OutputTrace.writeTestPath] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
            Challenge.EvmProof.Meter.instrStaticCost, hz])
      (by decide)
    simpa [gtest, gtestRaw, testStart, testEnd] using hraw
  let gbody := Output.gasSteps_writeBody q offset word j ret tail hj
    (by omega) htail qcode qfork qrun qnp
  have hbodyRun := OutputTrace.run_writeBody q offset word j ret tail hj
    (by omega) htail qcode qrun
  have hbody : gbody.cost + MachineState.memCost testEnd.activeWords.toNat =
      58 + MachineState.memCost
        (writeLoopState s offset word ret tail (j + 1)).activeWords.toNat := by
    have hraw := block_cost_potential OutputTrace.writeBodyPath testEnd
      { OutputTrace.writeByte q offset word j with
        pc := UInt256.ofNat 0x3c8
        stack := UInt256.ofNat (j + 1) :: UInt256.ofNat offset ::
          word :: ret :: tail } 58 qcode qfork (by simpa [testEnd] using hbodyRun)
      qrun qnp
      (by
        intro located hmem z hz
        simp [OutputTrace.writeBodyPath] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
            Challenge.EvmProof.Meter.instrStaticCost, hz])
      (by decide)
    simpa [gbody, Output.gasSteps_writeBody, testEnd, q, writeLoopState] using hraw
  have hjoined := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    gtest gbody 26 58 htest hbody
  simpa [gasSteps_writeIteration, gtest, gtestRaw, gbody,
    Output.gasSteps_writeBody, q, testStart, testEnd, writeLoopState,
    Nat.add_assoc] using hjoined

private theorem writeLoop_cost_potential (s : State) (offset : Nat)
    (word ret : UInt256) (tail : List UInt256)
    (htail : tail.length < 1016) (hoff : offset + 3 < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_writeLoop s offset word ret tail htail hoff hcode hfork
      hrun hnp).cost + MachineState.memCost
        (writeLoopState s offset word ret tail 0).activeWords.toNat =
      336 + MachineState.memCost
        (writeLoopState s offset word ret tail 4).activeWords.toNat := by
  unfold gasSteps_writeLoop
  simpa using Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
    4 84
    (fun j hj => gasSteps_writeIteration s offset word ret tail j hj
      htail hoff hcode hfork hrun hnp)
    (fun j hj => writeIteration_cost_potential s offset word ret tail j hj
      htail hoff hcode hfork hrun hnp)

set_option linter.unusedSimpArgs false in
private theorem writeWord_cost_potential (s : State) (offset : Nat)
    (word ret : UInt256) (tail : List UInt256)
    (htail : tail.length < 1016) (hoff : offset + 3 < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode ret.toNat = true) :
    (gasSteps_writeWord s offset word ret tail htail hoff hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      380 + MachineState.memCost
        (writeLoopState s offset word ret tail 4).activeWords.toNat := by
  let start : State := { s with
    pc := UInt256.ofNat 0x3c6
    stack := UInt256.ofNat offset :: word :: ret :: tail }
  let loop0 := writeLoopState s offset word ret tail 0
  have hinitRun : Challenge.EvmProof.Stepper.runLocatedBlock
      OutputTrace.writeInitPath start = some loop0 := by
    simpa [start, loop0, writeLoopState] using OutputTrace.run_writeInit s
      (UInt256.ofNat offset) word ret tail (by omega) hrun
  let ginit := Output.gasSteps_block OutputTrace.writeInitPath start loop0
    hcode hfork hinitRun hrun hnp
  have hinit : ginit.cost + MachineState.memCost start.activeWords.toNat =
      3 + MachineState.memCost loop0.activeWords.toNat := by
    exact block_cost_potential OutputTrace.writeInitPath start loop0 3 hcode
      hfork hinitRun hrun hnp
      (by
        intro located hmem q hq
        simp [OutputTrace.writeInitPath] at hmem
        rcases hmem with rfl | rfl <;>
          simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
            Challenge.EvmProof.Meter.instrStaticCost, hq])
      (by decide)
  let q := writeLoopState s offset word ret tail 4
  have qcode : q.executionEnv.code = referenceBytecode := by simpa [q] using hcode
  have qfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have qrun : q.halt = .Running := by simpa [q] using hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  let testEnd : State := { q with
    pc := UInt256.ofNat 0x3e9
    stack := UInt256.ofNat 4 :: UInt256.ofNat offset :: word :: ret :: tail }
  have htestRun : Challenge.EvmProof.Stepper.runLocatedBlock
      OutputTrace.writeTestPath q = some testEnd := by
    simpa [q, testEnd, writeLoopState] using OutputTrace.run_writeTest_exit q
      (UInt256.ofNat offset :: word :: ret :: tail) (by simp; omega) qcode qrun
  let gtest := Output.gasSteps_block OutputTrace.writeTestPath q testEnd
    qcode qfork htestRun qrun qnp
  have htest : gtest.cost + MachineState.memCost q.activeWords.toNat =
      26 + MachineState.memCost testEnd.activeWords.toNat := by
    exact block_cost_potential OutputTrace.writeTestPath q testEnd 26 qcode
      qfork htestRun qrun qnp
      (by
        intro located hmem z hz
        simp [OutputTrace.writeTestPath] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
            Challenge.EvmProof.Meter.instrStaticCost, hz])
      (by decide)
  let finish : State := { q with pc := ret, stack := tail }
  have hexitRun : Challenge.EvmProof.Stepper.runLocatedBlock
      OutputTrace.writeExitPath testEnd = some finish := by
    simpa [testEnd, finish] using OutputTrace.run_writeExit q
      (UInt256.ofNat offset) word ret tail (by omega) qcode qrun hvalid
  let gexit := Output.gasSteps_block OutputTrace.writeExitPath testEnd finish
    qcode qfork hexitRun qrun qnp
  have hexit : gexit.cost + MachineState.memCost testEnd.activeWords.toNat =
      15 + MachineState.memCost finish.activeWords.toNat := by
    exact block_cost_potential OutputTrace.writeExitPath testEnd finish 15 qcode
      qfork hexitRun qrun qnp
      (by
        intro located hmem z hz
        simp [OutputTrace.writeExitPath] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl <;>
          simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
            Challenge.EvmProof.Meter.instrStaticCost, hz])
      (by decide)
  have hloop := writeLoop_cost_potential s offset word ret tail htail hoff
    hcode hfork hrun hnp
  have hfirst := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    ginit (gasSteps_writeLoop s offset word ret tail htail hoff hcode hfork
      hrun hnp) 3 336 hinit (by simpa [loop0, q] using hloop)
  have hlast := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    gtest gexit 26 15 htest hexit
  have hall := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    (ginit.trans (gasSteps_writeLoop s offset word ret tail htail hoff hcode
      hfork hrun hnp)) (gtest.trans gexit) 339 41 hfirst hlast
  simpa [gasSteps_writeWord, ginit, gtest, gexit, start, loop0, q, testEnd,
    finish, Nat.add_assoc] using hall

set_option linter.unusedSimpArgs false in
private theorem outputIteration_cost_potential (s : State) (input : ByteArray)
    (i : Nat) (hi : i < 5)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_outputIteration s input i hi hcode hfork hrun hnp).cost +
        MachineState.memCost (outputLoopState s input i).activeWords.toNat =
      518 + MachineState.memCost
        (outputLoopState s input (i + 1)).activeWords.toNat := by
  let q := outputLoopState s input i
  have qcode : q.executionEnv.code = referenceBytecode := by simpa [q] using hcode
  have qfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have qrun : q.halt = .Running := by simpa [q] using hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  let conditionStart : State := { q with
    pc := UInt256.ofNat 0x654
    stack := [UInt256.ofNat i, Padding.paddedWord input] }
  let conditionEnd : State := { q with
    pc := UInt256.ofNat 0x65e
    stack := [UInt256.ofNat i, Padding.paddedWord input] }
  have hconditionRun : Challenge.EvmProof.Stepper.runLocatedBlock
      OutputTrace.outerTestPath conditionStart = some conditionEnd := by
    simpa [conditionStart, conditionEnd] using OutputTrace.run_outerTest_continue
      q i [Padding.paddedWord input] hi (by simp) qrun
  let gconditionRaw := Output.gasSteps_block OutputTrace.outerTestPath
    conditionStart conditionEnd qcode qfork hconditionRun qrun qnp
  let gcondition : GasSteps q conditionEnd := GasSteps.cast gconditionRaw
    (by simpa [q, conditionStart] using outputLoopState_normalized s input i) rfl
  have hcondition : gcondition.cost + MachineState.memCost q.activeWords.toNat =
      26 + MachineState.memCost conditionEnd.activeWords.toNat := by
    have hraw := block_cost_potential OutputTrace.outerTestPath conditionStart
      conditionEnd 26 qcode qfork hconditionRun qrun qnp
      (by
        intro located hmem z hz
        simp [OutputTrace.outerTestPath] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
            Challenge.EvmProof.Meter.instrStaticCost, hz])
      (by decide)
    simpa [gcondition, gconditionRaw, conditionStart, conditionEnd] using hraw
  let callEnd : State := { q with
    pc := UInt256.ofNat 0x20
    stack := [UInt256.ofNat i, ⟨0⟩, UInt256.ofNat 0x66a,
      UInt256.ofNat 0x676, UInt256.ofNat i, Padding.paddedWord input] }
  have hcallRun : Challenge.EvmProof.Stepper.runLocatedBlock
      OutputTrace.hAtCallPath conditionEnd = some callEnd := by
    simpa [conditionEnd, callEnd] using OutputTrace.run_hAtCall q i
      [Padding.paddedWord input] (by simp) qcode qrun
  let gcall := Output.gasSteps_block OutputTrace.hAtCallPath conditionEnd callEnd
    qcode qfork hcallRun qrun qnp
  have hcall : gcall.cost + MachineState.memCost conditionEnd.activeWords.toNat =
      22 + MachineState.memCost callEnd.activeWords.toNat := by
    exact block_cost_potential OutputTrace.hAtCallPath conditionEnd callEnd 22
      qcode qfork hcallRun qrun qnp
      (by
        intro located hmem z hz
        simp [OutputTrace.hAtCallPath] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
            Challenge.EvmProof.Meter.instrStaticCost, hz])
      (by decide)
  let hEnd : State := { loadedH q i with
    pc := UInt256.ofNat 0x66a
    stack := [OutputTrace.hWord q i, UInt256.ofNat 0x676,
      UInt256.ofNat i, Padding.paddedWord input] }
  have hhRun : Challenge.EvmProof.Stepper.runLocatedBlock
      OutputTrace.hAtPath callEnd = some hEnd := by
    simpa [callEnd, hEnd, loadedH] using OutputTrace.run_hAt q i
      [UInt256.ofNat 0x676, UInt256.ofNat i, Padding.paddedWord input]
      hi (by simp) qcode qrun
  let gh := Output.gasSteps_block OutputTrace.hAtPath callEnd hEnd
    qcode qfork hhRun qrun qnp
  have hh : gh.cost + MachineState.memCost callEnd.activeWords.toNat =
      37 + MachineState.memCost hEnd.activeWords.toNat := by
    exact block_cost_potential OutputTrace.hAtPath callEnd hEnd 37 qcode qfork
      hhRun qrun qnp
      (by
        intro located hmem z hz
        simp [OutputTrace.hAtPath] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl <;>
          simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
            Challenge.EvmProof.Meter.instrStaticCost, hz])
      (by decide)
  let loaded := loadedH q i
  have loadedCode : loaded.executionEnv.code = referenceBytecode := by
    simpa [loaded] using qcode
  have loadedFork : loaded.fork = .Osaka := by simpa [loaded, State.fork] using qfork
  have loadedRun : loaded.halt = .Running := by simpa [loaded] using qrun
  have loadedNp : Precompile.isPrecompileWithConfig loaded.executionEnv.precompileConfig loaded.executionEnv.fork
      loaded.executionEnv.codeAddr = false := by simpa [loaded] using qnp
  let writeStart : State := { loaded with
    pc := UInt256.ofNat 0x3c6
    stack := [UInt256.ofNat (12 + 4 * i), OutputTrace.hWord q i,
      UInt256.ofNat 0x676, UInt256.ofNat i, Padding.paddedWord input] }
  have hwcallRun : Challenge.EvmProof.Stepper.runLocatedBlock
      OutputTrace.writeCallPath hEnd = some writeStart := by
    simpa [hEnd, writeStart, loaded] using OutputTrace.run_writeCall loaded i
      (OutputTrace.hWord q i) [Padding.paddedWord input] hi (by simp)
      loadedCode loadedRun
  let gwcall := Output.gasSteps_block OutputTrace.writeCallPath hEnd writeStart
    loadedCode loadedFork hwcallRun loadedRun loadedNp
  have hwcall : gwcall.cost + MachineState.memCost hEnd.activeWords.toNat =
      27 + MachineState.memCost writeStart.activeWords.toNat := by
    exact block_cost_potential OutputTrace.writeCallPath hEnd writeStart 27
      loadedCode loadedFork hwcallRun loadedRun loadedNp
      (by
        intro located hmem z hz
        simp [OutputTrace.writeCallPath] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
            Challenge.EvmProof.Meter.instrStaticCost, hz])
      (by decide)
  let gwrite := gasSteps_writeWord loaded (12 + 4 * i)
    (OutputTrace.hWord q i) (UInt256.ofNat 0x676)
    [UInt256.ofNat i, Padding.paddedWord input] (by simp) (by omega)
    loadedCode loadedFork loadedRun loadedNp (by decide)
  let written := writeLoopState loaded (12 + 4 * i) (OutputTrace.hWord q i)
    (UInt256.ofNat 0x676) [UInt256.ofNat i, Padding.paddedWord input] 4
  have hwrite : gwrite.cost + MachineState.memCost writeStart.activeWords.toNat =
      380 + MachineState.memCost written.activeWords.toNat := by
    simpa [gwrite, writeStart, written] using writeWord_cost_potential loaded
      (12 + 4 * i) (OutputTrace.hWord q i) (UInt256.ofNat 0x676)
      [UInt256.ofNat i, Padding.paddedWord input] (by simp) (by omega)
      loadedCode loadedFork loadedRun loadedNp (by decide)
  have writtenCode : written.executionEnv.code = referenceBytecode := by
    simpa [written] using loadedCode
  have writtenFork : written.fork = .Osaka := by
    simpa [written, State.fork] using loadedFork
  have writtenRun : written.halt = .Running := by simpa [written] using loadedRun
  have writtenNp : Precompile.isPrecompileWithConfig written.executionEnv.precompileConfig written.executionEnv.fork
      written.executionEnv.codeAddr = false := by simpa [written] using loadedNp
  let writtenReturned : State := { written with
    pc := UInt256.ofNat 0x676
    stack := [UInt256.ofNat i, Padding.paddedWord input] }
  let next := afterWrittenWord q input i
  have hnextRun : Challenge.EvmProof.Stepper.runLocatedBlock
      OutputTrace.outerNextPath writtenReturned = some next := by
    simpa [writtenReturned, next, written, loaded, afterWrittenWord] using
      OutputTrace.run_outerNext written i [Padding.paddedWord input] hi
        (by simp) writtenCode writtenRun
  let gnext := Output.gasSteps_block OutputTrace.outerNextPath writtenReturned next
    writtenCode writtenFork hnextRun writtenRun writtenNp
  have hnext : gnext.cost + MachineState.memCost writtenReturned.activeWords.toNat =
      26 + MachineState.memCost next.activeWords.toNat := by
    exact block_cost_potential OutputTrace.outerNextPath writtenReturned next 26
      writtenCode writtenFork hnextRun writtenRun writtenNp
      (by
        intro located hmem z hz
        simp [OutputTrace.outerNextPath] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
            Challenge.EvmProof.Meter.instrStaticCost, hz])
      (by decide)
  have h12 := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    gcondition gcall 26 22 hcondition hcall
  have h34 := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    gh gwcall 37 27 hh hwcall
  have h56 := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    gwrite gnext 380 26 hwrite (by simpa [writtenReturned] using hnext)
  have h3456 := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    (gh.trans gwcall) (gwrite.trans gnext) 64 406 h34 h56
  have hall := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    (gcondition.trans gcall) ((gh.trans gwcall).trans (gwrite.trans gnext))
    48 470 h12 h3456
  simpa [gasSteps_outputIteration, gcondition, gconditionRaw, gcall, gh,
    gwcall, gwrite, gnext, q, conditionStart, conditionEnd, callEnd, hEnd,
    loaded, writeStart, written, writtenReturned, next, outputLoopState,
    Nat.add_assoc] using hall

private theorem outputLoop_cost_potential (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_outputLoop s input hcode hfork hrun hnp).cost +
        MachineState.memCost (outputLoopState s input 0).activeWords.toNat =
      2590 + MachineState.memCost
        (outputLoopState s input 5).activeWords.toNat := by
  unfold gasSteps_outputLoop
  simpa using Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
    5 518
    (fun i hi => gasSteps_outputIteration s input i hi hcode hfork hrun hnp)
    (fun i hi => outputIteration_cost_potential s input i hi hcode hfork hrun hnp)

private theorem activeWordsAfterUInt256_eq (s : State) (offset size : Nat)
    (hend : offset + size ≤ 32 * s.activeWords.toNat) :
    s.activeWordsAfterUInt256 offset size = s.activeWords := by
  unfold State.activeWordsAfterUInt256
  have haw : MachineState.activeWordsAfter s.activeWords.toNat offset size =
      s.activeWords.toNat := by
    unfold MachineState.activeWordsAfter
    by_cases hsize : size = 0
    · simp [hsize]
    · rw [if_neg hsize]
      have hpos : 0 < s.activeWords.toNat := by omega
      have hquot : (offset + size - 1) / 32 < s.activeWords.toNat := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        omega
      dsimp only
      exact Nat.max_eq_left (by omega)
  rw [haw]
  cases hword : s.activeWords with
  | mk val =>
      apply congrArg UInt256.mk
      apply Fin.ext
      simp [UInt256.toNat, Fin.ofNat,
        Nat.mod_eq_of_lt val.isLt]

private theorem writeLoopState_activeWords_eq (s : State) (offset : Nat)
    (word ret : UInt256) (tail : List UInt256) (j : Nat) (hj : j ≤ 4)
    (hbound : offset + 4 ≤ 32 * s.activeWords.toNat) :
    (writeLoopState s offset word ret tail j).activeWords = s.activeWords := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [writeLoopState]
      simp only [OutputTrace.writeByte]
      have hij : j ≤ 3 := by omega
      have hprev := ih (by omega)
      rw [activeWordsAfterUInt256_eq
        (writeLoopState s offset word ret tail j) (offset + j) 1]
      · exact hprev
      · rw [hprev]
        omega

private theorem outputLoopState_activeWords_eq (s : State) (input : ByteArray)
    (i : Nat) (hi : i ≤ 5) (hactive : 64 ≤ s.activeWords.toNat) :
    (outputLoopState s input i).activeWords = s.activeWords := by
  induction i with
  | zero =>
      unfold outputLoopState OutputTrace.zeroOutput
      exact activeWordsAfterUInt256_eq s 0 32 (by omega)
  | succ i ih =>
      have hii : i < 5 := by omega
      rw [outputLoopState]
      unfold afterWrittenWord loadedH
      simp only
      let prev := outputLoopState s input i
      have hprev : prev.activeWords = s.activeWords := ih (by omega)
      have hloaded : (prev.activeWordsAfterUInt256 (OutputTrace.hOffset i) 32) =
          s.activeWords := by
        rw [activeWordsAfterUInt256_eq prev (OutputTrace.hOffset i) 32]
        · exact hprev
        · rw [hprev]
          simp [OutputTrace.hOffset]
          omega
      have hwrite := writeLoopState_activeWords_eq
        { prev with activeWords := (prev.activeWordsAfterUInt256
            (OutputTrace.hOffset i) 32) }
        (12 + 4 * i) (OutputTrace.hWord prev i) (UInt256.ofNat 0x676)
        [UInt256.ofNat i, Padding.paddedWord input] 4 (by omega)
        (by simp [hloaded]; omega)
      simpa [prev, hloaded] using hwrite

private theorem outputResult_activeWords_eq (s : State) (input : ByteArray)
    (hactive : 64 ≤ s.activeWords.toNat) :
    (outputResult s input).activeWords = s.activeWords := by
  let q := outputLoopState s input 5
  have hq : q.activeWords = s.activeWords :=
    outputLoopState_activeWords_eq s input 5 (by omega) hactive
  change q.activeWordsAfterUInt256 0 32 = s.activeWords
  rw [activeWordsAfterUInt256_eq q 0 32]
  · exact hq
  · rw [hq]
    omega

set_option linter.unusedSimpArgs false in
private theorem output_cost_potential (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_output s input hcode hfork hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      2636 + MachineState.memCost (outputResult s input).activeWords.toNat := by
  let preStart := DriverTrace.afterExit s input
  let preEnd : State := { OutputTrace.zeroOutput s with
    pc := UInt256.ofNat 0x654, stack := [⟨0⟩, Padding.paddedWord input] }
  have hpreRun : Challenge.EvmProof.Stepper.runLocatedBlock
      OutputTrace.preludePath preStart = some preEnd := by
    simpa [preStart, preEnd, DriverTrace.afterExit] using OutputTrace.run_prelude s
      (DriverTrace.blockOffsetWord (DriverTrace.blockCount input))
      [Padding.paddedWord input] (by simp) hrun
  let gpre := Output.gasSteps_prelude s
    (DriverTrace.blockOffsetWord (DriverTrace.blockCount input))
    [Padding.paddedWord input] (by simp) hcode hfork hrun hnp
  have hpre : gpre.cost + MachineState.memCost s.activeWords.toNat =
      12 + MachineState.memCost (outputLoopState s input 0).activeWords.toNat := by
    have hraw := block_cost_potential OutputTrace.preludePath preStart preEnd 12
      hcode hfork hpreRun hrun hnp
      (by
        intro located hmem z hz
        simp [OutputTrace.preludePath] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
            Challenge.EvmProof.Meter.instrStaticCost, hz])
      (by decide)
    simpa [gpre, Output.gasSteps_prelude, preStart, preEnd, outputLoopState,
      DriverTrace.afterExit] using hraw
  let q := outputLoopState s input 5
  have qcode : q.executionEnv.code = referenceBytecode := by simpa [q] using hcode
  have qfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have qrun : q.halt = .Running := by simpa [q] using hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  let exitStart : State := { q with
    pc := UInt256.ofNat 0x654
    stack := [UInt256.ofNat 5, Padding.paddedWord input] }
  let exitEnd : State := { q with
    pc := UInt256.ofNat 0x681
    stack := [UInt256.ofNat 5, Padding.paddedWord input] }
  have hexitRun : Challenge.EvmProof.Stepper.runLocatedBlock
      OutputTrace.outerTestPath exitStart = some exitEnd := by
    simpa [exitStart, exitEnd, q] using OutputTrace.run_outerTest_exit q
      [Padding.paddedWord input] (by simp) qcode qrun
  let gexitRaw := Output.gasSteps_block OutputTrace.outerTestPath exitStart exitEnd
    qcode qfork hexitRun qrun qnp
  let gexit : GasSteps q exitEnd := GasSteps.cast gexitRaw
    (by simpa [q, exitStart] using outputLoopState_normalized s input 5) rfl
  have hexit : gexit.cost + MachineState.memCost q.activeWords.toNat =
      26 + MachineState.memCost exitEnd.activeWords.toNat := by
    have hraw := block_cost_potential OutputTrace.outerTestPath exitStart exitEnd
      26 qcode qfork hexitRun qrun qnp
      (by
        intro located hmem z hz
        simp [OutputTrace.outerTestPath] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
            Challenge.EvmProof.Meter.instrStaticCost, hz])
      (by decide)
    simpa [gexit, gexitRaw, exitStart, exitEnd] using hraw
  let gfinish := Output.gasSteps_finish q [Padding.paddedWord input]
    (by simp) qcode qfork qrun qnp
  have hfinishRun := OutputTrace.run_finish q [Padding.paddedWord input]
    (by simp) qrun
  have hfinish : gfinish.cost + MachineState.memCost exitEnd.activeWords.toNat =
      8 + MachineState.memCost (outputResult s input).activeWords.toNat := by
    have hraw := block_cost_potential OutputTrace.finishPath exitEnd
      (outputResult s input) 8 qcode qfork
      (by simpa [exitEnd, outputResult, q] using hfinishRun) qrun qnp
      (by
        intro located hmem z hz
        simp [OutputTrace.finishPath] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl <;>
          simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
            Challenge.EvmProof.Meter.instrStaticCost, hz])
      (by decide)
    simpa [gfinish, Output.gasSteps_finish, exitEnd] using hraw
  have hloop := outputLoop_cost_potential s input hcode hfork hrun hnp
  have hleft := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    gpre (gasSteps_outputLoop s input hcode hfork hrun hnp) 12 2590 hpre hloop
  have hright := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    gexit gfinish 26 8 hexit hfinish
  have hall := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    (gpre.trans (gasSteps_outputLoop s input hcode hfork hrun hnp))
    (gexit.trans gfinish) 2602 34 hleft hright
  simpa [gasSteps_output, gpre, gexit, gexitRaw, gfinish, q, exitStart,
    exitEnd, outputResult, Nat.add_assoc] using hall

private theorem output_cost (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hactive : 64 ≤ s.activeWords.toNat) :
    (gasSteps_output s input hcode hfork hrun hnp).cost = 2636 := by
  have hpotential := output_cost_potential s input hcode hfork hrun hnp
  rw [outputResult_activeWords_eq s input hactive] at hpotential
  omega

theorem framing_cost (input : ByteArray) (hfit : CalldataFits input)
    (seam : DirectCorrect.CompressionSeam input)
    (hactive : 64 ≤
      (seam.states (DriverTrace.blockCount input)).activeWords.toNat) :
    (DirectCorrect.fullTrace input hfit seam).cost =
      (PaddingTrace.gasSteps_pad input hfit).cost +
        (ExactGasBridge.loopTrace input hfit seam).cost +
          ExactGasBridge.framingWork := by
  unfold DirectCorrect.fullTrace
  simp only [Challenge.EvmProof.GasSteps.trans_cost]
  have hdriver : (gasSteps_driver input hfit seam).cost =
      3 + (ExactGasBridge.loopTrace input hfit seam).cost + 26 := by
    have hsetup : (DriverTrace.gasSteps_setup (seam.states 0) input
        (seam.code 0 (by omega)) (seam.fork 0 (by omega))
        (seam.running 0 (by omega)) (seam.noPrecompile 0 (by omega))).cost = 3 := by
      change Challenge.EvmProof.Stepper.runLocatedBlockCost
        DriverTrace.setupPath (DriverTrace.setupEntry (seam.states 0) input) = 3
      simp [DriverTrace.setupPath,
        Challenge.EvmProof.Stepper.runLocatedBlockCost,
        Challenge.EvmProof.Stepper.runLocated,
        Challenge.EvmProof.Stepper.runInstr, DriverTrace.setupEntry,
        seam.running 0 (by omega), Challenge.EvmProof.Stepper.instrCost,
        Gas.baseCost]
    let final := seam.states (DriverTrace.blockCount input)
    have hexit : (DriverTrace.gasSteps_condition_exit final input hfit
        (seam.code _ (by omega)) (seam.fork _ (by omega))
        (seam.running _ (by omega)) (seam.noPrecompile _ (by omega))).cost = 26 := by
      change Challenge.EvmProof.Stepper.runLocatedBlockCost DriverTrace.conditionPath
        (DriverTrace.loopAt final input (DriverTrace.blockCount input)) = 26
      have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
        DriverTrace.conditionPath
        (DriverTrace.run_condition_exit final input hfit
          (seam.code _ (by omega)) (seam.running _ (by omega)))
        (by simpa [final, DriverTrace.loopAt, State.fork] using
          seam.fork (DriverTrace.blockCount input) (by omega))
        (by
          intro located hmem q hq
          simp [DriverTrace.conditionPath] at hmem
          rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
              Challenge.EvmProof.Meter.instrStaticCost, hq])
      have haw : (DriverTrace.afterExit final input).activeWords =
          (DriverTrace.loopAt final input (DriverTrace.blockCount input)).activeWords := rfl
      rw [haw] at hmeter
      simpa [Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
        Challenge.EvmProof.Meter.instrStaticCost, Gas.baseCost,
        DriverTrace.conditionPath] using hmeter
    unfold gasSteps_driver ExactGasBridge.loopTrace
    simp only [Challenge.EvmProof.GasSteps.trans_cost,
      Challenge.EvmProof.GasSteps.cast_cost]
    rw [hsetup, hexit]
    omega
  rw [hdriver]
  have hout := output_cost
    (seam.states (DriverTrace.blockCount input)) input
    (seam.code _ (by omega)) (seam.fork _ (by omega))
    (seam.running _ (by omega)) (seam.noPrecompile _ (by omega)) hactive
  rw [hout]
  unfold ExactGasBridge.framingWork
  omega

/-- Concrete outer-trace costs. The final high-water premise is the state
endpoint fact established by the concrete compression seam's last schedule
load. -/
theorem outerCostFacts (input : ByteArray) (hfit : CalldataFits input)
    (seam : DirectCorrect.CompressionSeam input)
    (hfinal :
      (seam.states (DriverTrace.blockCount input)).activeWords.toNat =
        GasCost.finalActiveWords input.size) :
    ExactGasBridge.OuterCostFacts input hfit seam := by
  refine ⟨?_, seam_initial_activeWords input hfit seam, hfinal, ?_⟩
  · simpa [ExactGasBridge.paddingWork] using padding_cost input hfit
  · apply framing_cost input hfit seam
    rw [hfinal]
    simp [GasCost.finalActiveWords]
    omega

end Challenge.Ripemd160.Reference.Proofs.Bytecode.OuterGasTrace
