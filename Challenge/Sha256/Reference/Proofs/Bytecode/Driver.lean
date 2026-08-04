import Challenge.Sha256.Reference.Proofs.Bytecode.PaddingTrace
import Challenge.Sha256.Reference.Proofs.Bytecode.Compression
import Challenge.Sha256.Reference.Proofs.Bytecode.Output
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# Complete execution driver for the reference SHA-256 bytecode

This file connects the certified padding routine, the input-dependent outer
block loop, the compression summary, and the final digest-output block.  The
loop invariant is deliberately stated as exact EVM states, so another
bytecode proof can reuse the same block-indexed structure without depending
on the Yul source or compiler.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.Driver

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def setupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨711, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨712, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩]

def conditionPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨713, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨714, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨715, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨716, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨717, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨718, .push ⟨2, by decide⟩ (UInt256.ofNat 1401), by rfl, by decide⟩,
   ⟨719, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def callPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨720, .push ⟨2, by decide⟩ (UInt256.ofNat 1390), by rfl, by decide⟩,
   ⟨721, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨722, .push ⟨2, by decide⟩ (UInt256.ofNat Padding.messageOffset),
      by rfl, by decide⟩,
   ⟨723, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨724, .push ⟨2, by decide⟩ (UInt256.ofNat 612), by rfl, by decide⟩,
   ⟨725, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def incrementPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨726, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨727, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨728, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨729, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨730, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨731, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨732, .push ⟨2, by decide⟩ (UInt256.ofNat 1369), by rfl, by decide⟩,
   ⟨733, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem pc711 :
    Artifact.referenceArtifact.instructionPC 711 = 1367 := by decide
@[simp] private theorem pc712 :
    Artifact.referenceArtifact.instructionPC 712 = 1368 := by decide
@[simp] private theorem pc713 :
    Artifact.referenceArtifact.instructionPC 713 = 1369 := by decide
@[simp] private theorem pc714 :
    Artifact.referenceArtifact.instructionPC 714 = 1370 := by decide
@[simp] private theorem pc715 :
    Artifact.referenceArtifact.instructionPC 715 = 1371 := by decide
@[simp] private theorem pc716 :
    Artifact.referenceArtifact.instructionPC 716 = 1372 := by decide
@[simp] private theorem pc717 :
    Artifact.referenceArtifact.instructionPC 717 = 1373 := by decide
@[simp] private theorem pc718 :
    Artifact.referenceArtifact.instructionPC 718 = 1374 := by decide
@[simp] private theorem pc719 :
    Artifact.referenceArtifact.instructionPC 719 = 1377 := by decide
@[simp] private theorem pc720 :
    Artifact.referenceArtifact.instructionPC 720 = 1378 := by decide
@[simp] private theorem pc721 :
    Artifact.referenceArtifact.instructionPC 721 = 1381 := by decide
@[simp] private theorem pc722 :
    Artifact.referenceArtifact.instructionPC 722 = 1382 := by decide
@[simp] private theorem pc723 :
    Artifact.referenceArtifact.instructionPC 723 = 1385 := by decide
@[simp] private theorem pc724 :
    Artifact.referenceArtifact.instructionPC 724 = 1386 := by decide
@[simp] private theorem pc725 :
    Artifact.referenceArtifact.instructionPC 725 = 1389 := by decide
@[simp] private theorem pc726 :
    Artifact.referenceArtifact.instructionPC 726 = 1390 := by decide
@[simp] private theorem pc727 :
    Artifact.referenceArtifact.instructionPC 727 = 1391 := by decide
@[simp] private theorem pc728 :
    Artifact.referenceArtifact.instructionPC 728 = 1393 := by decide
@[simp] private theorem pc729 :
    Artifact.referenceArtifact.instructionPC 729 = 1394 := by decide
@[simp] private theorem pc730 :
    Artifact.referenceArtifact.instructionPC 730 = 1395 := by decide
@[simp] private theorem pc731 :
    Artifact.referenceArtifact.instructionPC 731 = 1396 := by decide
@[simp] private theorem pc732 :
    Artifact.referenceArtifact.instructionPC 732 = 1397 := by decide
@[simp] private theorem pc733 :
    Artifact.referenceArtifact.instructionPC 733 = 1400 := by decide

def blockCount (input : ByteArray) : Nat :=
  Padding.paddedLength input.size / 64

def blockOffset (i : Nat) : Nat := i * 64

def blockOffsetWord (i : Nat) : UInt256 := UInt256.ofNat (blockOffset i)

def messageOffsetWord (i : Nat) : UInt256 :=
  UInt256.ofNat (Padding.messageOffset + blockOffset i)

def loopAt (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 1369
    stack := [blockOffsetWord i, Padding.paddedWord input] }

def afterCondition (s : State) (input : ByteArray) (i : Nat) : State :=
  { loopAt s input i with pc := UInt256.ofNat 1378 }

def afterCompression (s : State) (input : ByteArray) (i : Nat) : State :=
  Compression.compressResult (loopAt s input i) (messageOffsetWord i)
    (UInt256.ofNat 1390) [blockOffsetWord i, Padding.paddedWord input]

def afterIteration (s : State) (input : ByteArray) (i : Nat) : State :=
  loopAt (afterCompression s input i) input (i + 1)

def blockLoopState (input : ByteArray) : Nat → State
  | 0 => loopAt (PaddingTrace.padReturned input) input 0
  | i + 1 => afterIteration (blockLoopState input i) input i

theorem paddedLength_eq_blockCount (input : ByteArray) :
    Padding.paddedLength input.size = blockCount input * 64 := by
  exact Padding.paddedLength_eq_blocks input.size

private theorem paddedLength_lt_uint256 (input : ByteArray)
    (hfit : CalldataFits input) :
    Padding.paddedLength input.size < 2 ^ 256 := by
  have hlt := Padding.paddedLength_lt input.size
  unfold CalldataFits at hfit
  norm_num at hfit ⊢
  omega

private theorem blockOffset_lt_uint256 (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i ≤ blockCount input) :
    blockOffset i < 2 ^ 256 := by
  have hpadded := paddedLength_lt_uint256 input hfit
  have heq := paddedLength_eq_blockCount input
  unfold blockOffset
  omega

private theorem messageOffset_lt_uint256 (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < blockCount input) :
    Padding.messageOffset + blockOffset i < 2 ^ 256 := by
  have hpad := Padding.paddedLength_lt input.size
  have hoff : blockOffset i < Padding.paddedLength input.size := by
    rw [paddedLength_eq_blockCount input]
    unfold blockOffset
    omega
  unfold CalldataFits at hfit
  norm_num [Padding.messageOffset] at hfit ⊢
  omega

private theorem offset_lt_total (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < blockCount input) :
    UInt256.lt (blockOffsetWord i) (Padding.paddedWord input) =
      UInt256.ofNat 1 := by
  have hoff := blockOffset_lt_uint256 input hfit i (Nat.le_of_lt hi)
  have hpad := paddedLength_lt_uint256 input hfit
  have hnat : blockOffset i < Padding.paddedLength input.size := by
    rw [paddedLength_eq_blockCount input]
    unfold blockOffset
    omega
  rw [Padding.paddedWord_eq input hfit]
  unfold UInt256.lt blockOffsetWord
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hoff, Nat.mod_eq_of_lt hpad]
  simp only [if_pos hnat]

private theorem offset_not_lt_total (input : ByteArray)
    (hfit : CalldataFits input) :
    UInt256.lt (blockOffsetWord (blockCount input))
      (Padding.paddedWord input) = 0 := by
  have hoff := blockOffset_lt_uint256 input hfit (blockCount input) (by omega)
  have hpad := paddedLength_lt_uint256 input hfit
  have heq : blockOffset (blockCount input) =
      Padding.paddedLength input.size := by
    rw [paddedLength_eq_blockCount input]
    rfl
  rw [Padding.paddedWord_eq input hfit]
  unfold UInt256.lt blockOffsetWord
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hoff, Nat.mod_eq_of_lt hpad, heq]
  simp only [Nat.lt_irrefl, if_false]
  rfl

@[simp] theorem loopAt_executionEnv (s : State) (input : ByteArray) (i : Nat) :
    (loopAt s input i).executionEnv = s.executionEnv := by rfl

@[simp] theorem loopAt_halt (s : State) (input : ByteArray) (i : Nat) :
    (loopAt s input i).halt = s.halt := by rfl

@[simp] theorem afterCompression_executionEnv (s : State) (input : ByteArray)
    (i : Nat) : (afterCompression s input i).executionEnv = s.executionEnv := by
  simp [afterCompression, Compression.compressResult,
    Compression.compressReturned, Compression.copyHashState,
    Compression.afterSchedule, Schedule.scheduleResult, Schedule.scheduleReturned]

@[simp] theorem afterCompression_halt (s : State) (input : ByteArray)
    (i : Nat) : (afterCompression s input i).halt = s.halt := by
  simp [afterCompression, Compression.compressResult,
    Compression.compressReturned, Compression.copyHashState,
    Compression.afterSchedule, Schedule.scheduleResult, Schedule.scheduleReturned]

@[simp] theorem afterIteration_executionEnv (s : State) (input : ByteArray)
    (i : Nat) : (afterIteration s input i).executionEnv = s.executionEnv := by
  simp [afterIteration]

@[simp] theorem afterIteration_halt (s : State) (input : ByteArray) (i : Nat) :
    (afterIteration s input i).halt = s.halt := by
  simp [afterIteration]

@[simp] theorem blockLoopState_executionEnv (input : ByteArray) (i : Nat) :
    (blockLoopState input i).executionEnv =
      (PaddingTrace.padReturned input).executionEnv := by
  induction i with
  | zero => rfl
  | succ i ih => simp [blockLoopState, ih]

@[simp] theorem blockLoopState_halt (input : ByteArray) (i : Nat) :
    (blockLoopState input i).halt =
      (PaddingTrace.padReturned input).halt := by
  induction i with
  | zero => rfl
  | succ i ih => simp [blockLoopState, ih]

@[simp] theorem loopAt_blockLoopState (input : ByteArray) (i : Nat) :
    loopAt (blockLoopState input i) input i = blockLoopState input i := by
  cases i <;> simp [blockLoopState, afterIteration, loopAt]

private theorem run_setup (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupPath
      (PaddingTrace.padReturned input) = some (blockLoopState input 0) := by
  simp [setupPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    blockLoopState, loopAt, blockOffsetWord, blockOffset]

def gasSteps_setup (input : ByteArray) :
    Challenge.EvmProof.GasSteps (PaddingTrace.padReturned input)
      (blockLoopState input 0) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka setupPath
  · rfl
  · rfl
  · exact run_setup input
  · rfl
  · rfl

theorem run_condition_continue (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < blockCount input)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock conditionPath (loopAt s input i) =
      some (afterCondition s input i) := by
  have hlt := offset_lt_total input hfit i hi
  have hzero : UInt256.isZero (UInt256.ofNat 1) = 0 := by decide
  have hfalse : UInt256.isTrue (0 : UInt256) = false := by decide
  simp [conditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopAt, afterCondition, hrun, hlt, hzero, hfalse]

theorem run_call (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < blockCount input)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock callPath
      (afterCondition s input i) =
      some (Compression.compressEntry (loopAt s input i)
        (messageOffsetWord i) (UInt256.ofNat 1390)
        [blockOffsetWord i, Padding.paddedWord input]) := by
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (messageOffset_lt_uint256 input hfit i hi)
  have hdest : Decode.isValidJumpDest referenceBytecode 612 = true := by decide
  simp [callPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterCondition, loopAt, Compression.compressEntry, messageOffsetWord,
    blockOffsetWord, hcode, hrun, hadd, hdest]

set_option linter.unusedSimpArgs false in
private theorem run_increment_core (q : State) (input : ByteArray) (i : Nat)
    (hcode : q.executionEnv.code = referenceBytecode)
    (hrun : q.halt = .Running)
    (hpc : q.pc = UInt256.ofNat 1390)
    (hstack : q.stack = [blockOffsetWord i, Padding.paddedWord input])
    (hadd : blockOffsetWord i + UInt256.ofNat 64 =
      blockOffsetWord (i + 1)) :
    Challenge.EvmProof.Stepper.runLocatedBlock incrementPath q =
      some { q with
        pc := UInt256.ofNat 1369
        stack := [blockOffsetWord (i + 1), Padding.paddedWord input] } := by
  have hdest : Decode.isValidJumpDest referenceBytecode 1369 = true := by decide
  simp [incrementPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpc, hstack, hcode, hrun, hadd, hdest, List.exchange]

theorem run_increment (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < blockCount input)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock incrementPath
      (afterCompression s input i) = some (afterIteration s input i) := by
  have hoff := blockOffset_lt_uint256 input hfit (i + 1) (by omega)
  have haddBound : i * 64 + 64 < 2 ^ 256 := by
    simpa [blockOffset, Nat.add_mul] using hoff
  have hadd : blockOffsetWord i + UInt256.ofNat 64 =
      blockOffsetWord (i + 1) := by
    simpa [blockOffsetWord, blockOffset, Nat.add_mul] using
      Challenge.EvmProof.Word.ofNat_add_ofNat (a := i * 64) (b := 64) haddBound
  have qcode : (afterCompression s input i).executionEnv.code =
      referenceBytecode := by simpa using hcode
  have qrun : (afterCompression s input i).halt = .Running := by
    simpa using hrun
  have qpc : (afterCompression s input i).pc = UInt256.ofNat 1390 := by
    rfl
  have qstack : (afterCompression s input i).stack =
      [blockOffsetWord i, Padding.paddedWord input] := by
    rfl
  have hcore := run_increment_core (afterCompression s input i) input i
    qcode qrun qpc qstack hadd
  simpa only [afterIteration, loopAt] using hcore

def gasSteps_iterationCondition (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < blockCount input)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopAt s input i)
      (afterCondition s input i) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka conditionPath
  · exact hcode
  · exact hfork
  · exact run_condition_continue s input hfit i hi hrun
  · exact hrun
  · exact hnp

@[simp] theorem gasSteps_iterationCondition_cost (s : State)
    (input : ByteArray) (hfit : CalldataFits input) (i : Nat)
    (hi : i < blockCount input)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_iterationCondition s input hfit i hi hcode hfork hrun hnp).cost =
      Challenge.EvmProof.Stepper.runLocatedBlockCost conditionPath
        (loopAt s input i) := by
  unfold gasSteps_iterationCondition
  rw [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]

def gasSteps_iterationCall (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < blockCount input)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (afterCondition s input i)
      (Compression.compressEntry (loopAt s input i) (messageOffsetWord i)
        (UInt256.ofNat 1390) [blockOffsetWord i, Padding.paddedWord input]) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka callPath
  · exact hcode
  · exact hfork
  · exact run_call s input hfit i hi hcode hrun
  · exact hrun
  · exact hnp

@[simp] theorem gasSteps_iterationCall_cost (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < blockCount input)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_iterationCall s input hfit i hi hcode hfork hrun hnp).cost =
      Challenge.EvmProof.Stepper.runLocatedBlockCost callPath
        (afterCondition s input i) := by
  unfold gasSteps_iterationCall
  rw [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]

def gasSteps_iterationCompress (s : State) (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (Compression.compressEntry (loopAt s input i) (messageOffsetWord i)
        (UInt256.ofNat 1390) [blockOffsetWord i, Padding.paddedWord input])
      (afterCompression s input i) := by
  have gCompress := Compression.gasSteps_compress (loopAt s input i)
    (messageOffsetWord i) (UInt256.ofNat 1390)
    [blockOffsetWord i, Padding.paddedWord input] (by simp)
    hcode hfork hrun hnp (by decide)
  exact Challenge.EvmProof.GasSteps.cast gCompress rfl (by
    simp [afterCompression])

@[simp] theorem gasSteps_iterationCompress_cost (s : State)
    (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_iterationCompress s input i hcode hfork hrun hnp).cost =
      (Compression.gasSteps_compress (loopAt s input i)
        (messageOffsetWord i) (UInt256.ofNat 1390)
        [blockOffsetWord i, Padding.paddedWord input] (by simp)
        hcode hfork hrun hnp (by decide)).cost := by
  unfold gasSteps_iterationCompress
  rw [Challenge.EvmProof.GasSteps.cast_cost]

def gasSteps_iterationIncrement (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < blockCount input)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (afterCompression s input i)
      (afterIteration s input i) := by
  have qcode : (afterCompression s input i).executionEnv.code =
      referenceBytecode := by simpa using hcode
  have qfork : (afterCompression s input i).fork = .Osaka := by
    simpa [State.fork] using hfork
  have qrun : (afterCompression s input i).halt = .Running := by
    simpa using hrun
  have qnp : Precompile.isPrecompile
      (afterCompression s input i).executionEnv.fork
      (afterCompression s input i).executionEnv.codeAddr = false := by
    simpa using hnp
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka incrementPath
  · exact qcode
  · exact qfork
  · exact run_increment s input hfit i hi hcode hrun
  · exact qrun
  · exact qnp

@[simp] theorem gasSteps_iterationIncrement_cost (s : State)
    (input : ByteArray) (hfit : CalldataFits input) (i : Nat)
    (hi : i < blockCount input)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_iterationIncrement s input hfit i hi hcode hfork hrun hnp).cost =
      Challenge.EvmProof.Stepper.runLocatedBlockCost incrementPath
        (afterCompression s input i) := by
  unfold gasSteps_iterationIncrement
  rw [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]

def gasSteps_iteration (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < blockCount input)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopAt s input i) (afterIteration s input i) :=
  (gasSteps_iterationCondition s input hfit i hi hcode hfork hrun hnp).trans
    ((gasSteps_iterationCall s input hfit i hi hcode hfork hrun hnp).trans
      ((gasSteps_iterationCompress s input i hcode hfork hrun hnp).trans
        (gasSteps_iterationIncrement s input hfit i hi hcode hfork hrun hnp)))

def gasSteps_blockLoopIteration (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < blockCount input) :
    Challenge.EvmProof.GasSteps (blockLoopState input i)
      (blockLoopState input (i + 1)) := by
  let q := blockLoopState input i
  have qcode : q.executionEnv.code = referenceBytecode := by
    simp [q]
  have qfork : q.fork = .Osaka := by simp [q, State.fork]
  have qrun : q.halt = .Running := by simp [q]
  have qnp : Precompile.isPrecompile q.executionEnv.fork
      q.executionEnv.codeAddr = false := by
    simpa [q, State.fork] using PaddingTrace.padReturned_noPrecompile input
  have g := gasSteps_iteration q input hfit i hi qcode qfork qrun qnp
  exact Challenge.EvmProof.GasSteps.cast g
    (by simp [q])
    (by simp [blockLoopState, q])

@[simp] theorem gasSteps_blockLoopIteration_cost (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < blockCount input) :
    (gasSteps_blockLoopIteration input hfit i hi).cost =
      (gasSteps_iteration (blockLoopState input i) input hfit i hi
        (by simp) (by simp [State.fork]) (by simp)
        (by simpa [State.fork] using
          PaddingTrace.padReturned_noPrecompile input)).cost := by
  unfold gasSteps_blockLoopIteration
  rw [Challenge.EvmProof.GasSteps.cast_cost]

def gasSteps_blockLoop (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (blockLoopState input 0)
      (blockLoopState input (blockCount input)) :=
  Challenge.EvmProof.GasSteps.iterateBounded (count := blockCount input)
    (gasSteps_blockLoopIteration input hfit)

@[simp] theorem gasSteps_blockLoop_cost (input : ByteArray)
    (hfit : CalldataFits input) :
    (gasSteps_blockLoop input hfit).cost =
      (Challenge.EvmProof.GasSteps.iterateBounded (count := blockCount input)
        (gasSteps_blockLoopIteration input hfit)).cost := rfl

private theorem run_condition_exit (input : ByteArray)
    (hfit : CalldataFits input) :
    Challenge.EvmProof.Stepper.runLocatedBlock conditionPath
      (blockLoopState input (blockCount input)) =
      some (Output.outputEntry (blockLoopState input (blockCount input))
        (blockOffsetWord (blockCount input)) [Padding.paddedWord input]) := by
  have hlt := offset_not_lt_total input hfit
  have hzero : UInt256.isZero (0 : UInt256) = UInt256.ofNat 1 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) = true := by decide
  have hdest : Decode.isValidJumpDest referenceBytecode 1401 = true := by decide
  conv_lhs =>
    rw [← loopAt_blockLoopState input (blockCount input)]
  simp [conditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopAt, Output.outputEntry, hlt, hzero, htrue, hdest]

def gasSteps_exit (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (blockLoopState input (blockCount input))
      (Output.outputEntry (blockLoopState input (blockCount input))
        (blockOffsetWord (blockCount input)) [Padding.paddedWord input]) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka conditionPath
  · simp [Artifact.referenceArtifact]
  · simp [State.fork]
  · exact run_condition_exit input hfit
  · simp
  · simpa [State.fork] using PaddingTrace.padReturned_noPrecompile input

/-- Complete direct execution of the reference artifact from the fixed initial
state through padding, every message block, and `RETURN`. -/
def gasSteps_reference (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (Output.outputResult (blockLoopState input (blockCount input))
        [Padding.paddedWord input]) := by
  let final := blockLoopState input (blockCount input)
  have finalCode : final.executionEnv.code = referenceBytecode := by
    simp [final]
  have finalFork : final.fork = .Osaka := by simp [final, State.fork]
  have finalRun : final.halt = .Running := by simp [final]
  have finalNp : Precompile.isPrecompile final.executionEnv.fork
      final.executionEnv.codeAddr = false := by
    simpa [final, State.fork] using PaddingTrace.padReturned_noPrecompile input
  have output := Output.gasSteps_output final
    (blockOffsetWord (blockCount input)) [Padding.paddedWord input]
    (by simp) finalCode finalFork finalRun finalNp
  exact (PaddingTrace.gasSteps_pad input hfit).trans
    ((gasSteps_setup input).trans
      ((gasSteps_blockLoop input hfit).trans
        ((gasSteps_exit input hfit).trans (by simpa [final] using output))))

end Challenge.Sha256.Reference.Proofs.Bytecode.Driver
