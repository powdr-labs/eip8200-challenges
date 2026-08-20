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

private def outputConditionStart (q : State) (input : ByteArray) (i : Nat) : State :=
  { q with
    pc := UInt256.ofNat 0x654
    stack := [UInt256.ofNat i, Padding.paddedWord input] }

private def outputConditionEnd (q : State) (input : ByteArray) (i : Nat) : State :=
  { q with
    pc := UInt256.ofNat 0x65e
    stack := [UInt256.ofNat i, Padding.paddedWord input] }

private def outputCallEnd (q : State) (input : ByteArray) (i : Nat) : State :=
  { q with
    pc := UInt256.ofNat 0x20
    stack := [UInt256.ofNat i, ⟨0⟩, UInt256.ofNat 0x66a,
      UInt256.ofNat 0x676, UInt256.ofNat i, Padding.paddedWord input] }

private def outputHEnd (q : State) (input : ByteArray) (i : Nat) : State :=
  { loadedH q i with
    pc := UInt256.ofNat 0x66a
    stack := [OutputTrace.hWord q i, UInt256.ofNat 0x676,
      UInt256.ofNat i, Padding.paddedWord input] }

private def outputWriteStart (q : State) (input : ByteArray) (i : Nat) : State :=
  { loadedH q i with
    pc := UInt256.ofNat 0x3c6
    stack := [UInt256.ofNat (12 + 4 * i), OutputTrace.hWord q i,
      UInt256.ofNat 0x676, UInt256.ofNat i, Padding.paddedWord input] }

private def outputWritten (q : State) (input : ByteArray) (i : Nat) : State :=
  writeLoopState (loadedH q i) (12 + 4 * i) (OutputTrace.hWord q i)
    (UInt256.ofNat 0x676) [UInt256.ofNat i, Padding.paddedWord input] 4

private def outputWrittenReturned (q : State) (input : ByteArray) (i : Nat) : State :=
  { outputWritten q input i with
    pc := UInt256.ofNat 0x676
    stack := [UInt256.ofNat i, Padding.paddedWord input] }

private def gasSteps_outputCondition (s : State) (input : ByteArray)
    (i : Nat) (hi : i < 5)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps (outputLoopState s input i)
      (outputConditionEnd (outputLoopState s input i) input i) := by
  let q := outputLoopState s input i
  have raw : GasSteps (outputConditionStart q input i)
      (outputConditionEnd q input i) := by
    apply Output.gasSteps_block OutputTrace.outerTestPath
    · simpa [q, outputConditionStart] using hcode
    · simpa [q, outputConditionStart, State.fork] using hfork
    · simpa [outputConditionStart, outputConditionEnd] using
        OutputTrace.run_outerTest_continue q i [Padding.paddedWord input]
          hi (by simp) (by simpa [q] using hrun)
    · simpa [q, outputConditionStart] using hrun
    · simpa [q, outputConditionStart] using hnp
  exact GasSteps.cast raw
    (by simpa [q, outputConditionStart] using outputLoopState_normalized s input i) rfl

private def gasSteps_outputCall (s : State) (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps (outputConditionEnd (outputLoopState s input i) input i)
      (outputCallEnd (outputLoopState s input i) input i) := by
  let q := outputLoopState s input i
  apply Output.gasSteps_block OutputTrace.hAtCallPath
  · simpa [q, outputConditionEnd] using hcode
  · simpa [q, outputConditionEnd, State.fork] using hfork
  · simpa [q, outputConditionEnd, outputCallEnd] using
      OutputTrace.run_hAtCall q i [Padding.paddedWord input] (by simp)
        (by simpa [q] using hcode) (by simpa [q] using hrun)
  · simpa [q, outputConditionEnd] using hrun
  · simpa [q, outputConditionEnd] using hnp

private def gasSteps_outputH (s : State) (input : ByteArray) (i : Nat)
    (hi : i < 5) (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps (outputCallEnd (outputLoopState s input i) input i)
      (outputHEnd (outputLoopState s input i) input i) := by
  let q := outputLoopState s input i
  apply Output.gasSteps_block OutputTrace.hAtPath
  · simpa [q, outputCallEnd] using hcode
  · simpa [q, outputCallEnd, State.fork] using hfork
  · simpa [q, outputCallEnd, outputHEnd, loadedH] using
      OutputTrace.run_hAt q i
        [UInt256.ofNat 0x676, UInt256.ofNat i, Padding.paddedWord input]
        hi (by simp) (by simpa [q] using hcode) (by simpa [q] using hrun)
  · simpa [q, outputCallEnd] using hrun
  · simpa [q, outputCallEnd] using hnp

private def gasSteps_outputWriteCall (s : State) (input : ByteArray) (i : Nat)
    (hi : i < 5) (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps (outputHEnd (outputLoopState s input i) input i)
      (outputWriteStart (outputLoopState s input i) input i) := by
  let q := outputLoopState s input i
  let loaded := loadedH q i
  apply Output.gasSteps_block OutputTrace.writeCallPath
  · simpa [q, loaded, outputHEnd] using hcode
  · simpa [q, loaded, outputHEnd, State.fork] using hfork
  · simpa [q, outputHEnd, outputWriteStart, loaded] using
      OutputTrace.run_writeCall loaded i (OutputTrace.hWord q i)
        [Padding.paddedWord input] hi (by simp)
        (by simpa [q, loaded] using hcode) (by simpa [q, loaded] using hrun)
  · simpa [q, loaded, outputHEnd] using hrun
  · simpa [q, loaded, outputHEnd] using hnp

private def gasSteps_outputWrite (s : State) (input : ByteArray) (i : Nat)
    (hi : i < 5)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps (outputWriteStart (outputLoopState s input i) input i)
      (outputWrittenReturned (outputLoopState s input i) input i) := by
  let q := outputLoopState s input i
  let gone := gasSteps_writeWord (loadedH q i) (12 + 4 * i)
      (OutputTrace.hWord q i)
      (UInt256.ofNat 0x676) [UInt256.ofNat i, Padding.paddedWord input]
      (by simp) (by omega) (by simpa [q] using hcode)
      (by simpa [q, State.fork] using hfork) (by simpa [q] using hrun)
      (by simpa [q] using hnp) (by decide)
  exact GasSteps.cast gone
    (by simp [q, gone, outputWriteStart])
    (by simp [q, gone, outputWrittenReturned, outputWritten])

private def gasSteps_outputNext (s : State) (input : ByteArray) (i : Nat)
    (hi : i < 5) (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps (outputWrittenReturned (outputLoopState s input i) input i)
      (outputLoopState s input (i + 1)) := by
  let q := outputLoopState s input i
  let written := outputWritten q input i
  have raw : GasSteps (outputWrittenReturned q input i)
      (afterWrittenWord q input i) := by
    apply Output.gasSteps_block OutputTrace.outerNextPath
    · simpa [q, written, outputWrittenReturned, outputWritten] using hcode
    · simpa [q, written, outputWrittenReturned, outputWritten, State.fork] using hfork
    · simpa [q, outputWrittenReturned, written, outputWritten,
        afterWrittenWord] using
        OutputTrace.run_outerNext written i [Padding.paddedWord input] hi
          (by simp) (by simpa [q, written, outputWritten] using hcode)
          (by simpa [q, written, outputWritten] using hrun)
    · simpa [q, written, outputWrittenReturned, outputWritten] using hrun
    · simpa [q, written, outputWrittenReturned, outputWritten] using hnp
  exact GasSteps.cast raw rfl (by rfl)

@[simp] private theorem gasSteps_outputCondition_cost (s : State)
    (input : ByteArray) (i : Nat) (hi : i < 5)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_outputCondition s input i hi hcode hfork hrun hnp).cost =
      Challenge.EvmProof.Stepper.runLocatedBlockCost OutputTrace.outerTestPath
        (outputConditionStart (outputLoopState s input i) input i) := by
  rfl

@[simp] private theorem gasSteps_outputCall_cost (s : State)
    (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_outputCall s input i hcode hfork hrun hnp).cost =
      Challenge.EvmProof.Stepper.runLocatedBlockCost OutputTrace.hAtCallPath
        (outputConditionEnd (outputLoopState s input i) input i) := by
  rfl

@[simp] private theorem gasSteps_outputH_cost (s : State)
    (input : ByteArray) (i : Nat) (hi : i < 5)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_outputH s input i hi hcode hfork hrun hnp).cost =
      Challenge.EvmProof.Stepper.runLocatedBlockCost OutputTrace.hAtPath
        (outputCallEnd (outputLoopState s input i) input i) := by
  rfl

@[simp] private theorem gasSteps_outputWriteCall_cost (s : State)
    (input : ByteArray) (i : Nat) (hi : i < 5)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_outputWriteCall s input i hi hcode hfork hrun hnp).cost =
      Challenge.EvmProof.Stepper.runLocatedBlockCost OutputTrace.writeCallPath
        (outputHEnd (outputLoopState s input i) input i) := by
  rfl

@[simp] private theorem gasSteps_outputNext_cost (s : State)
    (input : ByteArray) (i : Nat) (hi : i < 5)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_outputNext s input i hi hcode hfork hrun hnp).cost =
      Challenge.EvmProof.Stepper.runLocatedBlockCost OutputTrace.outerNextPath
        (outputWrittenReturned (outputLoopState s input i) input i) := by
  rfl

private def gasSteps_outputIteration (s : State) (input : ByteArray)
    (i : Nat) (hi : i < 5)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps (outputLoopState s input i) (outputLoopState s input (i + 1)) :=
  (gasSteps_outputCondition s input i hi hcode hfork hrun hnp).trans
    ((gasSteps_outputCall s input i hcode hfork hrun hnp).trans
    ((gasSteps_outputH s input i hi hcode hfork hrun hnp).trans
    ((gasSteps_outputWriteCall s input i hi hcode hfork hrun hnp).trans
    ((gasSteps_outputWrite s input i hi hcode hfork hrun hnp).trans
      (gasSteps_outputNext s input i hi hcode hfork hrun hnp)))))

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

private noncomputable def gasSteps_outputRawCost (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : Nat := by
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
  exact gpre.cost + ((gasSteps_outputLoop s input hcode hfork hrun hnp).cost +
    (gexit.cost + gfinish.cost))

@[simp] private theorem gasSteps_output_cost (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_output s input hcode hfork hrun hnp).cost =
      gasSteps_outputRawCost s input hcode hfork hrun hnp := by
  rfl

@[simp] private theorem gasSteps_outputRawCost_eq (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    gasSteps_outputRawCost s input hcode hfork hrun hnp =
      Challenge.EvmProof.Stepper.runLocatedBlockCost OutputTrace.preludePath
          (DriverTrace.afterExit s input) +
        ((gasSteps_outputLoop s input hcode hfork hrun hnp).cost +
          (Challenge.EvmProof.Stepper.runLocatedBlockCost OutputTrace.outerTestPath
              (outputLoopState s input 5) +
            Challenge.EvmProof.Stepper.runLocatedBlockCost OutputTrace.finishPath
              { outputLoopState s input 5 with
                pc := UInt256.ofNat 0x681
                stack := [UInt256.ofNat 5, Padding.paddedWord input] })) := by
  rfl

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

@[simp] private theorem gasSteps_driver_cost (input : ByteArray)
    (hfit : CalldataFits input) (seam : CompressionSeam input) :
    (gasSteps_driver input hfit seam).cost =
      (DriverTrace.gasSteps_setup (seam.states 0) input
        (seam.code 0 (by omega)) (seam.fork 0 (by omega))
        (seam.running 0 (by omega)) (seam.noPrecompile 0 (by omega))).cost +
      ((DriverTrace.gasSteps_loop_of_compress seam.states input hfit
        seam.code seam.fork seam.running seam.noPrecompile seam.compress).cost +
      (DriverTrace.gasSteps_condition_exit
        (seam.states (DriverTrace.blockCount input)) input hfit
        (seam.code _ (by omega)) (seam.fork _ (by omega))
        (seam.running _ (by omega)) (seam.noPrecompile _ (by omega))).cost) := by
  rfl

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
