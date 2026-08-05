import Challenge.Ripemd160.Reference.Proofs.Bytecode.DriverTrace
import Challenge.Ripemd160.Reference.Proofs.Bytecode.Output
import Challenge.Ripemd160.Reference.Proofs.Bytecode.GasCost
import Challenge.Ripemd160.Reference.Proofs.Bytecode.HashSpecBridge

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-!
# Conditional end-to-end direct-bytecode certificate

Everything outside compression is discharged here: initialization and
padding, the post-padding block driver, the complete five-word output loop,
and `RETURN(0, 32)`.  `CompressionSeam` is the single remaining interface. It
asks for one gas-parametric compression trace per padded block and records the
five final chaining words produced by those traces.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.DirectCorrect

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM

private def loadedH (s : State) (i : Nat) : State :=
  { s with activeWords := s.activeWordsAfterUInt256 (OutputTrace.hOffset i) 32 }

private def writeLoopState (s : State) (offset : Nat) (word ret : UInt256)
    (tail : List UInt256) : Nat → State
  | 0 => { s with
      pc := UInt256.ofNat 0x3c8
      stack := [⟨0⟩, UInt256.ofNat offset, word, ret] ++ tail }
  | j + 1 => { OutputTrace.writeByte (writeLoopState s offset word ret tail j)
        offset word j with
      pc := UInt256.ofNat 0x3c8
      stack := [UInt256.ofNat (j + 1), UInt256.ofNat offset, word, ret] ++ tail }

@[simp] private theorem writeLoopState_executionEnv (s : State) (offset : Nat)
    (word ret : UInt256) (tail : List UInt256) (j : Nat) :
    (writeLoopState s offset word ret tail j).executionEnv = s.executionEnv := by
  induction j with
  | zero => rfl
  | succ j ih => simp [writeLoopState, OutputTrace.writeByte, ih]

@[simp] private theorem writeLoopState_halt (s : State) (offset : Nat)
    (word ret : UInt256) (tail : List UInt256) (j : Nat) :
    (writeLoopState s offset word ret tail j).halt = s.halt := by
  induction j with
  | zero => rfl
  | succ j ih => simp [writeLoopState, OutputTrace.writeByte, ih]

@[simp] private theorem writeLoopState_callStack (s : State) (offset : Nat)
    (word ret : UInt256) (tail : List UInt256) (j : Nat) :
    (writeLoopState s offset word ret tail j).callStack = s.callStack := by
  induction j with
  | zero => rfl
  | succ j ih => simp [writeLoopState, OutputTrace.writeByte, ih]

private theorem writeLoopState_normalized (s : State) (offset : Nat)
    (word ret : UInt256) (tail : List UInt256) (j : Nat) :
    { writeLoopState s offset word ret tail j with
      pc := UInt256.ofNat 0x3c8
      stack := UInt256.ofNat j :: UInt256.ofNat offset :: word :: ret :: tail } =
      writeLoopState s offset word ret tail j := by
  cases j <;> rfl

private def afterWrittenWord (s : State) (input : ByteArray) (i : Nat) : State :=
  let loaded := loadedH s i
  let written := writeLoopState loaded (12 + 4 * i) (OutputTrace.hWord s i)
    (UInt256.ofNat 0x676) [UInt256.ofNat i, Padding.paddedWord input] 4
  { written with
    pc := UInt256.ofNat 0x654
    stack := [UInt256.ofNat (i + 1), Padding.paddedWord input] }

private def outputLoopState (s : State) (input : ByteArray) : Nat → State
  | 0 => { OutputTrace.zeroOutput s with
      pc := UInt256.ofNat 0x654
      stack := [⟨0⟩, Padding.paddedWord input] }
  | i + 1 => afterWrittenWord (outputLoopState s input i) input i

@[simp] private theorem outputLoopState_executionEnv (s : State)
    (input : ByteArray) (i : Nat) :
    (outputLoopState s input i).executionEnv = s.executionEnv := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [outputLoopState, afterWrittenWord, loadedH, ih]

@[simp] private theorem outputLoopState_halt (s : State)
    (input : ByteArray) (i : Nat) :
    (outputLoopState s input i).halt = s.halt := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [outputLoopState, afterWrittenWord, loadedH, ih]

@[simp] private theorem outputLoopState_pc (s : State)
    (input : ByteArray) (i : Nat) :
    (outputLoopState s input i).pc = UInt256.ofNat 0x654 := by
  cases i <;> rfl

@[simp] private theorem outputLoopState_stack (s : State)
    (input : ByteArray) (i : Nat) :
    (outputLoopState s input i).stack =
      [UInt256.ofNat i, Padding.paddedWord input] := by
  cases i with
  | zero => rfl
  | succ i => rfl

@[simp] private theorem outputLoopState_callStack (s : State)
    (input : ByteArray) (i : Nat) :
    (outputLoopState s input i).callStack = s.callStack := by
  induction i with
  | zero => rfl
  | succ i ih => simp [outputLoopState, afterWrittenWord, loadedH, ih]

private theorem outputLoopState_normalized (s : State) (input : ByteArray)
    (i : Nat) :
    { outputLoopState s input i with
      pc := UInt256.ofNat 0x654
      stack := [UInt256.ofNat i, Padding.paddedWord input] } =
      outputLoopState s input i := by
  cases i <;> rfl

@[simp] private theorem loadedH_executionEnv (s : State) (i : Nat) :
    (loadedH s i).executionEnv = s.executionEnv := rfl

@[simp] private theorem loadedH_halt (s : State) (i : Nat) :
    (loadedH s i).halt = s.halt := rfl

private def outputResult (s : State) (input : ByteArray) : State :=
  let q := outputLoopState s input 5
  { q with
    pc := UInt256.ofNat 0x686
    stack := [Padding.paddedWord input]
    halt := .Returned
    hReturn := MachineState.readPadded q.memory 0 32
    activeWords := q.activeWordsAfterUInt256 0 32 }

private def gasSteps_writeIteration (s : State) (offset : Nat)
    (word ret : UInt256) (tail : List UInt256) (j : Nat) (hj : j < 4)
    (htail : tail.length < 1016) (hoff : offset + 3 < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps (writeLoopState s offset word ret tail j)
      (writeLoopState s offset word ret tail (j + 1)) := by
  let q := writeLoopState s offset word ret tail j
  have qcode : q.executionEnv.code = referenceBytecode := by simpa [q] using hcode
  have qfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have qrun : q.halt = .Running := by simpa [q] using hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  have gtestRaw : GasSteps
      { q with
        pc := UInt256.ofNat 0x3c8
        stack := UInt256.ofNat j :: UInt256.ofNat offset :: word :: ret :: tail }
      { q with
        pc := UInt256.ofNat 0x3d2
        stack := UInt256.ofNat j :: UInt256.ofNat offset :: word :: ret :: tail } := by
    apply Output.gasSteps_block OutputTrace.writeTestPath
    · exact qcode
    · exact qfork
    · simpa using
        OutputTrace.run_writeTest_continue q j
          (UInt256.ofNat offset :: word :: ret :: tail) hj (by simp; omega) qrun
    · exact qrun
    · exact qnp
  have gtest : GasSteps q
      { q with
        pc := UInt256.ofNat 0x3d2
        stack := UInt256.ofNat j :: UInt256.ofNat offset :: word :: ret :: tail } :=
    GasSteps.cast gtestRaw
      (by simpa [q] using writeLoopState_normalized s offset word ret tail j) rfl
  have gbody := Output.gasSteps_writeBody q offset word j ret tail hj
    (by omega) htail qcode qfork qrun qnp
  exact GasSteps.cast (gtest.trans gbody) rfl (by rfl)

private def gasSteps_writeLoop (s : State) (offset : Nat)
    (word ret : UInt256) (tail : List UInt256)
    (htail : tail.length < 1016) (hoff : offset + 3 < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps (writeLoopState s offset word ret tail 0)
      (writeLoopState s offset word ret tail 4) :=
  GasSteps.iterateBounded (count := 4) (I := writeLoopState s offset word ret tail)
    (fun j hj => gasSteps_writeIteration s offset word ret tail j hj
      htail hoff hcode hfork hrun hnp)

private def gasSteps_writeWord (s : State) (offset : Nat) (word ret : UInt256)
    (tail : List UInt256)
    (htail : tail.length < 1016) (hoff : offset + 3 < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode ret.toNat = true) :
    GasSteps
      { s with
        pc := UInt256.ofNat 0x3c6
        stack := UInt256.ofNat offset :: word :: ret :: tail }
      { writeLoopState s offset word ret tail 4 with pc := ret, stack := tail } := by
  have ginit : GasSteps
      { s with
        pc := UInt256.ofNat 0x3c6
        stack := UInt256.ofNat offset :: word :: ret :: tail }
      (writeLoopState s offset word ret tail 0) := by
    apply Output.gasSteps_block OutputTrace.writeInitPath
    · exact hcode
    · exact hfork
    · simpa [writeLoopState] using OutputTrace.run_writeInit s
        (UInt256.ofNat offset) word ret tail (by omega) hrun
    · exact hrun
    · exact hnp
  let q := writeLoopState s offset word ret tail 4
  have qcode : q.executionEnv.code = referenceBytecode := by simpa [q] using hcode
  have qfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have qrun : q.halt = .Running := by simpa [q] using hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  have gtest : GasSteps q
      { q with
        pc := UInt256.ofNat 0x3e9
        stack := UInt256.ofNat 4 :: UInt256.ofNat offset :: word :: ret :: tail } := by
    apply Output.gasSteps_block OutputTrace.writeTestPath
    · exact qcode
    · exact qfork
    · simpa [q, writeLoopState] using OutputTrace.run_writeTest_exit q
        (UInt256.ofNat offset :: word :: ret :: tail) (by simp; omega) qcode qrun
    · exact qrun
    · exact qnp
  have gexit : GasSteps
      { q with
        pc := UInt256.ofNat 0x3e9
        stack := UInt256.ofNat 4 :: UInt256.ofNat offset :: word :: ret :: tail }
      { q with pc := ret, stack := tail } := by
    apply Output.gasSteps_block OutputTrace.writeExitPath
    · exact qcode
    · exact qfork
    · simpa using OutputTrace.run_writeExit q (UInt256.ofNat offset) word ret
        tail (by omega) qcode qrun hvalid
    · exact qrun
    · exact qnp
  exact ginit.trans ((gasSteps_writeLoop s offset word ret tail htail hoff hcode hfork
    hrun hnp).trans (gtest.trans gexit))

private def gasSteps_outputIteration (s : State) (input : ByteArray)
    (i : Nat) (hi : i < 5)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps (outputLoopState s input i) (outputLoopState s input (i + 1)) := by
  let q := outputLoopState s input i
  have qcode : q.executionEnv.code = referenceBytecode := by simpa [q] using hcode
  have qfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have qrun : q.halt = .Running := by simpa [q] using hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  have gconditionRaw : GasSteps
      { q with
        pc := UInt256.ofNat 0x654
        stack := [UInt256.ofNat i, Padding.paddedWord input] }
      { q with
        pc := UInt256.ofNat 0x65e
        stack := [UInt256.ofNat i, Padding.paddedWord input] } := by
    apply Output.gasSteps_block OutputTrace.outerTestPath
    · exact qcode
    · exact qfork
    · simpa using OutputTrace.run_outerTest_continue q i
        [Padding.paddedWord input] hi (by simp) qrun
    · exact qrun
    · exact qnp
  have gcondition : GasSteps q
      { q with
        pc := UInt256.ofNat 0x65e
        stack := [UInt256.ofNat i, Padding.paddedWord input] } :=
    GasSteps.cast gconditionRaw
      (by simpa [q] using outputLoopState_normalized s input i) rfl
  have gcall : GasSteps
      { q with
        pc := UInt256.ofNat 0x65e
        stack := [UInt256.ofNat i, Padding.paddedWord input] }
      { q with
        pc := UInt256.ofNat 0x20
        stack := [UInt256.ofNat i, ⟨0⟩, UInt256.ofNat 0x66a,
          UInt256.ofNat 0x676, UInt256.ofNat i, Padding.paddedWord input] } := by
    apply Output.gasSteps_block OutputTrace.hAtCallPath
    · exact qcode
    · exact qfork
    · simpa using OutputTrace.run_hAtCall q i [Padding.paddedWord input]
        (by simp) qcode qrun
    · exact qrun
    · exact qnp
  have gh : GasSteps
      { q with
        pc := UInt256.ofNat 0x20
        stack := [UInt256.ofNat i, ⟨0⟩, UInt256.ofNat 0x66a,
          UInt256.ofNat 0x676, UInt256.ofNat i, Padding.paddedWord input] }
      { loadedH q i with
        pc := UInt256.ofNat 0x66a
        stack := [OutputTrace.hWord q i, UInt256.ofNat 0x676,
          UInt256.ofNat i, Padding.paddedWord input] } := by
    apply Output.gasSteps_block OutputTrace.hAtPath
    · exact qcode
    · exact qfork
    · simpa [loadedH] using OutputTrace.run_hAt q i
        [UInt256.ofNat 0x676, UInt256.ofNat i, Padding.paddedWord input]
        hi (by simp) qcode qrun
    · exact qrun
    · exact qnp
  let loaded := loadedH q i
  have loadedCode : loaded.executionEnv.code = referenceBytecode := by
    change q.executionEnv.code = referenceBytecode
    exact qcode
  have loadedFork : loaded.fork = .Osaka := by
    change q.executionEnv.fork = .Osaka
    exact qfork
  have loadedRun : loaded.halt = .Running := by
    change q.halt = .Running
    exact qrun
  have loadedNp : Precompile.isPrecompileWithConfig loaded.executionEnv.precompileConfig loaded.executionEnv.fork
      loaded.executionEnv.codeAddr = false := by
    change Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false
    exact qnp
  have gwcall : GasSteps
      { loaded with
        pc := UInt256.ofNat 0x66a
        stack := [OutputTrace.hWord q i, UInt256.ofNat 0x676,
          UInt256.ofNat i, Padding.paddedWord input] }
      { loaded with
        pc := UInt256.ofNat 0x3c6
        stack := [UInt256.ofNat (12 + 4 * i), OutputTrace.hWord q i,
          UInt256.ofNat 0x676, UInt256.ofNat i, Padding.paddedWord input] } := by
    apply Output.gasSteps_block OutputTrace.writeCallPath
    · exact loadedCode
    · exact loadedFork
    · simpa using OutputTrace.run_writeCall loaded i (OutputTrace.hWord q i)
        [Padding.paddedWord input] hi (by simp) loadedCode loadedRun
    · exact loadedRun
    · exact loadedNp
  have gwrite := gasSteps_writeWord loaded (12 + 4 * i)
    (OutputTrace.hWord q i) (UInt256.ofNat 0x676)
    [UInt256.ofNat i, Padding.paddedWord input] (by simp) (by omega)
    loadedCode loadedFork loadedRun
    loadedNp (by decide)
  let written := writeLoopState loaded (12 + 4 * i) (OutputTrace.hWord q i)
    (UInt256.ofNat 0x676) [UInt256.ofNat i, Padding.paddedWord input] 4
  have writtenCode : written.executionEnv.code = referenceBytecode := by
    simpa [written] using loadedCode
  have writtenFork : written.fork = .Osaka := by
    simpa [written, State.fork] using loadedFork
  have writtenRun : written.halt = .Running := by simpa [written] using loadedRun
  have writtenNp : Precompile.isPrecompileWithConfig written.executionEnv.precompileConfig written.executionEnv.fork
      written.executionEnv.codeAddr = false := by simpa [written] using loadedNp
  have gnext : GasSteps
      { written with
        pc := UInt256.ofNat 0x676
        stack := [UInt256.ofNat i, Padding.paddedWord input] }
      (afterWrittenWord q input i) := by
    apply Output.gasSteps_block OutputTrace.outerNextPath
    · exact writtenCode
    · exact writtenFork
    · simpa [afterWrittenWord, written, loaded] using
        OutputTrace.run_outerNext written i [Padding.paddedWord input] hi
          (by simp) writtenCode writtenRun
    · exact writtenRun
    · exact writtenNp
  exact GasSteps.cast
    (gcondition.trans (gcall.trans (gh.trans (gwcall.trans (gwrite.trans gnext)))))
    rfl (by rfl)

private def gasSteps_outputLoop (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps (outputLoopState s input 0) (outputLoopState s input 5) :=
  GasSteps.iterateBounded (count := 5) (I := outputLoopState s input)
    (fun i hi => gasSteps_outputIteration s input i hi hcode hfork hrun hnp)

private def gasSteps_output (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.afterExit s input) (outputResult s input) := by
  have gpre := Output.gasSteps_prelude s
    (DriverTrace.blockOffsetWord (DriverTrace.blockCount input))
    [Padding.paddedWord input] (by simp) hcode hfork hrun hnp
  let q := outputLoopState s input 5
  have qcode : q.executionEnv.code = referenceBytecode := by simpa [q] using hcode
  have qfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have qrun : q.halt = .Running := by simpa [q] using hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  have gexitRaw : GasSteps
      { q with
        pc := UInt256.ofNat 0x654
        stack := [UInt256.ofNat 5, Padding.paddedWord input] }
      { q with
        pc := UInt256.ofNat 0x681
        stack := [UInt256.ofNat 5, Padding.paddedWord input] } := by
    apply Output.gasSteps_block OutputTrace.outerTestPath
    · exact qcode
    · exact qfork
    · simpa [q] using OutputTrace.run_outerTest_exit q
        [Padding.paddedWord input] (by simp) qcode qrun
    · exact qrun
    · exact qnp
  have gexit : GasSteps q
      { q with
        pc := UInt256.ofNat 0x681
        stack := [UInt256.ofNat 5, Padding.paddedWord input] } :=
    GasSteps.cast gexitRaw
      (by simpa [q] using outputLoopState_normalized s input 5) rfl
  have gfinish := Output.gasSteps_finish q [Padding.paddedWord input]
    (by simp) qcode qfork qrun qnp
  exact GasSteps.cast
    (gpre.trans ((gasSteps_outputLoop s input hcode hfork hrun hnp).trans
      (gexit.trans gfinish)))
    rfl rfl

/-- The one remaining end-to-end hypothesis: a certified compression trace
for each padded block, plus the resulting five mathematical chaining words. -/
structure CompressionSeam (input : ByteArray) where
  states : Nat → State
  initial : DriverTrace.setupEntry (states 0) input = PaddingTrace.padReturned input
  code : ∀ i, i ≤ DriverTrace.blockCount input →
    (states i).executionEnv.code = referenceBytecode
  fork : ∀ i, i ≤ DriverTrace.blockCount input →
    (states i).fork = .Osaka
  running : ∀ i, i ≤ DriverTrace.blockCount input →
    (states i).halt = .Running
  noPrecompile : ∀ i, i ≤ DriverTrace.blockCount input →
    Precompile.isPrecompileWithConfig (states i).executionEnv.precompileConfig (states i).executionEnv.fork
      (states i).executionEnv.codeAddr = false
  callStack : ∀ i, i ≤ DriverTrace.blockCount input →
    (states i).callStack = []
  compress : ∀ i, i < DriverTrace.blockCount input →
    GasSteps (DriverTrace.compressEntry (states i) input i)
      (DriverTrace.compressReturned (states (i + 1)) input i)
  finalWords : ∀ i : Fin 5,
    OutputTrace.hWord (states (DriverTrace.blockCount input)) i =
      Challenge.EvmProof.Word.ofUInt32
      (SpecBridge.absorbBlocks EvmSemantics.Crypto.Ripemd160.H0
          (Padding.paddedMessage input) 0
          (DriverTrace.blockCount input))[i]!

private noncomputable def gasSteps_driver (input : ByteArray)
    (hfit : CalldataFits input) (seam : CompressionSeam input) :
    GasSteps (PaddingTrace.padReturned input)
      (DriverTrace.afterExit (seam.states (DriverTrace.blockCount input)) input) := by
  have gsetup := DriverTrace.gasSteps_setup (seam.states 0) input
    (seam.code 0 (by omega)) (seam.fork 0 (by omega))
    (seam.running 0 (by omega)) (seam.noPrecompile 0 (by omega))
  have gloop := DriverTrace.gasSteps_loop_of_compress seam.states input hfit
    seam.code seam.fork seam.running seam.noPrecompile seam.compress
  let final := seam.states (DriverTrace.blockCount input)
  have gexit := DriverTrace.gasSteps_condition_exit final input hfit
    (seam.code _ (by omega)) (seam.fork _ (by omega))
    (seam.running _ (by omega)) (seam.noPrecompile _ (by omega))
  exact GasSteps.cast (gsetup.trans (gloop.trans gexit)) seam.initial
    (by simp [final, DriverTrace.afterExit])

noncomputable def fullTrace (input : ByteArray) (hfit : CalldataFits input)
    (seam : CompressionSeam input) :
    GasSteps (initialState referenceBytecode input 0)
      (outputResult (seam.states (DriverTrace.blockCount input)) input) := by
  let final := seam.states (DriverTrace.blockCount input)
  have gout := gasSteps_output final input (seam.code _ (by omega))
    (seam.fork _ (by omega)) (seam.running _ (by omega))
    (seam.noPrecompile _ (by omega))
  exact (PaddingTrace.gasSteps_pad input hfit).trans
    ((gasSteps_driver input hfit seam).trans (by simpa [final] using gout))

/-- Conditional exact-gas connection to the closed schedule in `GasCost`.
All control-flow costs are already carried by `fullTrace`; the remaining cost
identity is precisely the compression-cost telescope. -/
theorem correctWithSchedule_of_compression
    (seam : ∀ (input : ByteArray), CalldataFits input → CompressionSeam input)
    (hcost : ∀ (input : ByteArray) (hfit : CalldataFits input),
      (fullTrace input hfit (seam input hfit)).cost = GasCost.referenceGas input)
    (hresult : ∀ (input : ByteArray) (hfit : CalldataFits input),
      (outputResult
        ((seam input hfit).states (DriverTrace.blockCount input)) input).toResult =
          .returned (spec input)) :
    GasCost.CorrectWithSchedule referenceBytecode GasCost.referenceGasForSize := by
  apply GasCost.gasSchedule_correct_of_trace
    (finalState := fun input hfit => outputResult
      ((seam input hfit).states (DriverTrace.blockCount input)) input)
    (fullTrace := fun input hfit => fullTrace input hfit (seam input hfit))
  · exact hcost
  · intro input hfit
    simp [outputResult, State.isDone, State.isHalted, State.isRunning,
      (seam input hfit).callStack (DriverTrace.blockCount input) (by omega)]
  · exact hresult

/-- The same conditional certificate, projected to the challenge's minimal
eventual-sufficiency statement. -/
theorem correct_of_compression
    (seam : ∀ (input : ByteArray), CalldataFits input → CompressionSeam input)
    (hcost : ∀ (input : ByteArray) (hfit : CalldataFits input),
      (fullTrace input hfit (seam input hfit)).cost = GasCost.referenceGas input)
    (hresult : ∀ (input : ByteArray) (hfit : CalldataFits input),
      (outputResult
        ((seam input hfit).states (DriverTrace.blockCount input)) input).toResult =
          .returned (spec input)) :
    Correct referenceBytecode :=
  GasCost.correct_of_schedule
    (correctWithSchedule_of_compression seam hcost hresult)

end Challenge.Ripemd160.Reference.Proofs.Bytecode.DirectCorrect
