import Challenge.Ripemd160.Reference.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Reference.Proofs.Bytecode.Trace
import Challenge.EvmProof.Stepper
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
/-!
# Direct execution of the RIPEMD-160 padding function

The fixed setup and the eight-iteration little-endian footer loop are exposed
as located paths.  The resulting state is shared by correctness and exact gas
accounting.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.PaddingTrace

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def pushedReturn (input : ByteArray) : State :=
  { Main.initializedState input with
    pc := (Main.initializedState input).pc + UInt256.ofNat 3
    stack := UInt256.ofNat 0x62c :: (Main.initializedState input).stack }

def pushedOutput (input : ByteArray) : State :=
  { pushedReturn input with
    pc := (pushedReturn input).pc.succ
    stack := ⟨0⟩ :: (pushedReturn input).stack }

def pushedPad (input : ByteArray) : State :=
  { pushedOutput input with
    pc := (pushedOutput input).pc + UInt256.ofNat 3
    stack := UInt256.ofNat 0x1e0 :: (pushedOutput input).stack }

def padEntry (input : ByteArray) : State :=
  { pushedPad input with
    pc := UInt256.ofNat 0x1e0
    stack := [⟨0⟩, UInt256.ofNat 0x62c] }

@[simp] private theorem padEntry_halt (input : ByteArray) :
    (padEntry input).halt = .Running := by rfl

@[simp] private theorem padEntry_fork (input : ByteArray) :
    (padEntry input).fork = .Osaka := by rfl

@[simp] private theorem padEntry_code (input : ByteArray) :
    (padEntry input).executionEnv.code = referenceBytecode := by rfl

@[simp] private theorem padEntry_calldata (input : ByteArray) :
    (padEntry input).executionEnv.calldata = input := by rfl

@[simp] private theorem initializedPC764 :
    Artifact.instructionPC 764 = 0x624 := by rfl

@[simp] private theorem initializedCalldata (input : ByteArray) :
    (Main.initializedState input).executionEnv.calldata = input := by rfl

def enterPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  Artifact.padEnterPath

@[simp] private theorem validPadEntry :
    Decode.isValidJumpDest referenceBytecode 0x1e0 = true := by
  rw [← Artifact.refPc349]
  exact Artifact.referenceArtifact.isValidJumpDest_index 349 (by rfl)

set_option maxHeartbeats 200000 in
private theorem run_enter (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock enterPath
      (Main.initializedState input) = some (padEntry input) := by
  simp [enterPath, Artifact.padEnterPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    pushedReturn, pushedOutput, pushedPad, padEntry]

def gasSteps_enterPad (input : ByteArray) :
    Challenge.EvmProof.GasSteps (Main.initializedState input) (padEntry input) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka enterPath
  · rfl
  · rfl
  · exact run_enter input
  · rfl
  · exact deployAddress_not_precompile

def paddedLengthPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  Artifact.padLengthPath

def padLengthReady (input : ByteArray) : State :=
  { padEntry input with
    pc := UInt256.ofNat (Artifact.instructionPC 360)
    stack := [UInt256.ofNat input.size, Padding.paddedWord input,
      UInt256.ofNat 0x62c] }

@[simp] private theorem padLengthReady_halt (input : ByteArray) :
    (padLengthReady input).halt = .Running := by rfl

@[simp] private theorem padLengthReady_fork (input : ByteArray) :
    (padLengthReady input).fork = .Osaka := by rfl

@[simp] private theorem padLengthReady_code (input : ByteArray) :
    (padLengthReady input).executionEnv.code = referenceBytecode := by rfl

@[simp] private theorem padLengthReady_calldata (input : ByteArray) :
    (padLengthReady input).executionEnv.calldata = input := by rfl

@[simp] private theorem padLengthReady_pcToNat (input : ByteArray) :
    (padLengthReady input).pc.toNat = 0x1ee := by rfl

@[simp] private theorem padLengthReady_pc (input : ByteArray) :
    (padLengthReady input).pc = UInt256.ofNat 0x1ee := by rfl

@[simp] private theorem padLengthReady_pcSucc (input : ByteArray) :
    (padLengthReady input).pc.succ = UInt256.ofNat 0x1ef := by
  rw [padLengthReady_pc, Challenge.EvmProof.Word.succ_ofNat (by norm_num)]

@[simp] private theorem padLengthReady_stack (input : ByteArray) :
    (padLengthReady input).stack =
      [UInt256.ofNat input.size, Padding.paddedWord input, UInt256.ofNat 0x62c] := by
  rfl

set_option maxHeartbeats 200000 in
private theorem run_paddedLength (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock paddedLengthPath (padEntry input) =
      some (padLengthReady input) := by
  simp [paddedLengthPath, Artifact.padLengthPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    padEntry, pushedPad, pushedOutput, pushedReturn, padLengthReady,
    Padding.paddedWord, List.exchange]

def gasSteps_paddedLength (input : ByteArray) :
    Challenge.EvmProof.GasSteps (padEntry input) (padLengthReady input) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka paddedLengthPath
  · rfl
  · rfl
  · exact run_paddedLength input
  · rfl
  · exact deployAddress_not_precompile

def bitLengthWord (input : ByteArray) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat input.size) (UInt256.ofNat 3)

def lengthOffsetWord (input : ByteArray) : UInt256 :=
  UInt256.ofNat Padding.messageOffset +
    (Padding.paddedWord input - UInt256.ofNat 8)

def padCopied (input : ByteArray) : State :=
  { padLengthReady input with
    pc := UInt256.ofNat (Artifact.instructionPC 364)
    memory := MachineState.writeBytes (padLengthReady input).memory
      (MachineState.readPadded input 0 input.size) Padding.messageOffset
    activeWords := (padLengthReady input).activeWordsAfterUInt256
      Padding.messageOffset input.size }

def padSentinel (input : ByteArray) : State :=
  { padCopied input with
    pc := UInt256.ofNat (Artifact.instructionPC 369)
    stack := [UInt256.ofNat input.size, Padding.paddedWord input,
      UInt256.ofNat 0x62c]
    memory := MachineState.writeBytes (padCopied input).memory
      (ByteArray.mk #[0x80]) (Padding.messageOffset + input.size)
    activeWords := (padCopied input).activeWordsAfterUInt256
      (Padding.messageOffset + input.size) 1 }

@[simp] private theorem padCopied_halt (input : ByteArray) :
    (padCopied input).halt = .Running := by rfl

@[simp] private theorem padCopied_pcToNat (input : ByteArray) :
    (padCopied input).pc.toNat = 0x1f4 := by rfl

@[simp] private theorem padCopied_pc (input : ByteArray) :
    (padCopied input).pc = UInt256.ofNat 0x1f4 := by rfl

@[simp] private theorem padCopied_stack (input : ByteArray) :
    (padCopied input).stack =
      [UInt256.ofNat input.size, Padding.paddedWord input, UInt256.ofNat 0x62c] := by
  rfl

@[simp] private theorem padCopied_calldata (input : ByteArray) :
    (padCopied input).executionEnv.calldata = input := by rfl

@[simp] private theorem padSentinel_halt (input : ByteArray) :
    (padSentinel input).halt = .Running := by rfl

@[simp] private theorem padSentinel_pcToNat (input : ByteArray) :
    (padSentinel input).pc.toNat = 0x1fc := by rfl

@[simp] private theorem padSentinel_stack (input : ByteArray) :
    (padSentinel input).stack =
      [UInt256.ofNat input.size, Padding.paddedWord input, UInt256.ofNat 0x62c] := by
  rfl

def lengthLoopStart (input : ByteArray) : State :=
  { padSentinel input with
    pc := UInt256.ofNat (Artifact.instructionPC 378)
    stack := [⟨0⟩, lengthOffsetWord input, bitLengthWord input,
      UInt256.ofNat input.size, Padding.paddedWord input, UInt256.ofNat 0x62c] }

@[simp] private theorem lengthLoopStart_halt (input : ByteArray) :
    (lengthLoopStart input).halt = .Running := by rfl

def lengthSetupPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  Artifact.padSetupPath

def lengthCopyPath := lengthSetupPath.take 4
def lengthSentinelPath := (lengthSetupPath.drop 4).take 5
def lengthFooterSetupPath := (lengthSetupPath.drop 9).dropLast
def lengthSentinelAddressPath := lengthSentinelPath.take 4
def lengthSentinelStorePath := lengthSentinelPath.drop 4

def padSentinelAddressReady (input : ByteArray) : State :=
  { padCopied input with
    pc := UInt256.ofNat (Artifact.instructionPC 368)
    stack := [UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size,
      UInt256.ofNat 128, UInt256.ofNat input.size, Padding.paddedWord input,
      UInt256.ofNat 0x62c] }

def padSentinelStored (input : ByteArray) : State :=
  { padSentinelAddressReady input with
    pc := UInt256.ofNat (Artifact.instructionPC 369)
    stack := [UInt256.ofNat input.size, Padding.paddedWord input,
      UInt256.ofNat 0x62c]
    memory := MachineState.writeBytes (padSentinelAddressReady input).memory
      (ByteArray.mk #[0x80])
      (UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size).toNat
    activeWords := (padSentinelAddressReady input).activeWordsAfterUInt256
      (UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size).toNat 1 }

@[simp] private theorem padSentinelAddressReady_halt (input : ByteArray) :
    (padSentinelAddressReady input).halt = .Running := by rfl

@[simp] private theorem padSentinelAddressReady_pc (input : ByteArray) :
    (padSentinelAddressReady input).pc = UInt256.ofNat 0x1fb := by rfl

@[simp] private theorem padSentinelAddressReady_stack (input : ByteArray) :
    (padSentinelAddressReady input).stack =
      [UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size,
        UInt256.ofNat 128, UInt256.ofNat input.size, Padding.paddedWord input,
        UInt256.ofNat 0x62c] := by rfl

@[simp] private theorem padSentinelAddressReady_memory (input : ByteArray) :
    (padSentinelAddressReady input).memory = (padCopied input).memory := by rfl

@[simp] private theorem padSentinelAddressReady_activeWords (input : ByteArray) :
    (padSentinelAddressReady input).activeWords = (padCopied input).activeWords := by rfl

set_option maxHeartbeats 200000 in
private theorem run_lengthCopy (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthCopyPath
      (padLengthReady input) = some (padCopied input) := by
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hsizeWord : (UInt256.ofNat input.size).toNat = input.size := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize]
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by rfl
  simp [lengthCopyPath, lengthSetupPath, Artifact.padSetupPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    padCopied, State.activeWordsAfterUInt256, Padding.messageOffset,
    hsizeWord, hzero]

set_option maxHeartbeats 200000 in
private theorem run_lengthSentinelAddress (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthSentinelAddressPath
      (padCopied input) = some (padSentinelAddressReady input) := by
  simp [lengthSentinelAddressPath, lengthSentinelPath, lengthSetupPath,
    Artifact.padSetupPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    padSentinelAddressReady, Padding.messageOffset]

set_option maxHeartbeats 200000 in
private theorem run_lengthSentinelStore (input : ByteArray)
    (_hfit : CalldataFits input) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthSentinelStorePath
      (padSentinelAddressReady input) = some (padSentinelStored input) := by
  simp [lengthSentinelStorePath, lengthSentinelPath, lengthSetupPath,
    Artifact.padSetupPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    padSentinelStored, State.activeWordsAfterUInt256]

private theorem padSentinelStored_eq (input : ByteArray)
    (hfit : CalldataFits input) : padSentinelStored input = padSentinel input := by
  have hsum : Padding.messageOffset + input.size < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num [Padding.messageOffset] at hfit ⊢
    omega
  have hadd : UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size =
      UInt256.ofNat (Padding.messageOffset + input.size) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat hsum
  have haddNat : (UInt256.ofNat Padding.messageOffset +
      UInt256.ofNat input.size).toNat = Padding.messageOffset + input.size := by
    rw [hadd, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hsum]
  unfold padSentinelStored padSentinel padSentinelAddressReady
  rw [show (UInt256.ofNat Padding.messageOffset +
    UInt256.ofNat input.size).toNat = Padding.messageOffset + input.size by
      exact haddNat]
  generalize padCopied input = s
  cases s
  rfl

set_option maxHeartbeats 200000 in
private theorem run_lengthFooterSetup (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthFooterSetupPath
      (padSentinel input) = some (lengthLoopStart input) := by
  simp [lengthFooterSetupPath, lengthSetupPath, Artifact.padSetupPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthLoopStart, padSentinel, padCopied, lengthOffsetWord,
    bitLengthWord, Padding.messageOffset]

def gasSteps_lengthSetup (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (padLengthReady input)
      (lengthLoopStart input) := by
  have g₁ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthCopyPath (by rfl) (by rfl)
    (run_lengthCopy input hfit) (by rfl) deployAddress_not_precompile
  have g₂ₐ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthSentinelAddressPath (by rfl) (by rfl)
    (run_lengthSentinelAddress input) (by rfl) deployAddress_not_precompile
  have g2raw := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthSentinelStorePath (by rfl) (by rfl)
    (run_lengthSentinelStore input hfit) (by rfl) deployAddress_not_precompile
  have g2b := Challenge.EvmProof.GasSteps.cast g2raw rfl
    (padSentinelStored_eq input hfit)
  have g₂ := g₂ₐ.trans g2b
  have g₃ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthFooterSetupPath (by rfl) (by rfl)
    (run_lengthFooterSetup input) (by rfl) deployAddress_not_precompile
  exact g₁.trans (g₂.trans g₃)

/-! ## Eight-byte little-endian footer loop -/

def lengthByteWord (input : ByteArray) (i : Nat) : UInt256 :=
  UInt256.land
    (UInt256.shiftRight (bitLengthWord input)
      (UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 3)))
    (UInt256.ofNat 255)

def lengthLoopMemory (input : ByteArray) : Nat → ByteArray
  | 0 => (padSentinel input).memory
  | i + 1 => MachineState.writeBytes (lengthLoopMemory input i)
      (ByteArray.mk #[UInt8.ofNat ((lengthByteWord input i).toNat % 256)])
      (lengthOffsetWord input + UInt256.ofNat i).toNat

def lengthLoopActiveWords (input : ByteArray) : Nat → UInt256
  | 0 => (padSentinel input).activeWords
  | i + 1 => UInt256.ofNat (MachineState.activeWordsAfter
      (lengthLoopActiveWords input i).toNat
      (lengthOffsetWord input + UInt256.ofNat i).toNat 1)

def lengthLoopState (input : ByteArray) (i : Nat) : State :=
  { lengthLoopStart input with
    pc := UInt256.ofNat (Artifact.instructionPC 378)
    stack := [UInt256.ofNat i, lengthOffsetWord input, bitLengthWord input,
      UInt256.ofNat input.size, Padding.paddedWord input, UInt256.ofNat 0x62c]
    memory := lengthLoopMemory input i
    activeWords := lengthLoopActiveWords input i }

@[simp] theorem lengthLoopState_zero (input : ByteArray) :
    lengthLoopState input 0 = lengthLoopStart input := by
  unfold lengthLoopState lengthLoopMemory lengthLoopActiveWords
    lengthLoopStart
  generalize padSentinel input = s
  cases s
  rfl

def lengthIterationPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨378, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨379, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨380, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨381, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨382, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨383, .push ⟨2, by decide⟩ (UInt256.ofNat 0x22a), by rfl, by decide⟩,
   ⟨384, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨385, .push ⟨1, by decide⟩ (UInt256.ofNat 255), by rfl, by decide⟩,
   ⟨386, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨387, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨388, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨389, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨390, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨391, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨392, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨393, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨394, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨395, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨396, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨397, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨398, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨399, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨400, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨401, .push ⟨2, by decide⟩ (UInt256.ofNat 0x209), by rfl, by decide⟩,
   ⟨402, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem lengthLoopState_halt (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).halt = .Running := by rfl

@[simp] private theorem lengthLoopState_fork (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).fork = .Osaka := by rfl

@[simp] private theorem lengthLoopState_code (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).executionEnv.code = referenceBytecode := by rfl

@[simp] private theorem lengthLoopState_pcToNat (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).pc.toNat = 0x209 := by rfl

@[simp] private theorem lengthLoopState_pc (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).pc = UInt256.ofNat 0x209 := by rfl

@[simp] private theorem lengthLoopState_pcSucc (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).pc.succ = UInt256.ofNat 0x20a := by
  rw [lengthLoopState_pc, Challenge.EvmProof.Word.succ_ofNat (by norm_num)]

@[simp] private theorem lengthLoopState_stack (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).stack =
      [UInt256.ofNat i, lengthOffsetWord input, bitLengthWord input,
        UInt256.ofNat input.size, Padding.paddedWord input, UInt256.ofNat 0x62c] := by
  rfl

def lengthConditionPath := lengthIterationPath.take 7
def lengthBytePath := (lengthIterationPath.drop 7).take 7
def lengthStorePath := (lengthIterationPath.drop 14).take 4
def lengthIncrementPath := (lengthIterationPath.drop 18).take 5
def lengthBackPath := lengthIterationPath.drop 23
def lengthBackPushPath := lengthBackPath.take 1
def lengthBackJumpPath := lengthBackPath.drop 1

def lengthBodyState (input : ByteArray) (i : Nat) : State :=
  { lengthLoopState input i with pc := UInt256.ofNat (Artifact.instructionPC 385) }

def lengthByteState (input : ByteArray) (i : Nat) : State :=
  { lengthBodyState input i with
    pc := UInt256.ofNat (Artifact.instructionPC 392)
    stack := [lengthByteWord input i, UInt256.ofNat i, lengthOffsetWord input,
      bitLengthWord input, UInt256.ofNat input.size, Padding.paddedWord input,
      UInt256.ofNat 0x62c] }

def lengthStoredState (input : ByteArray) (i : Nat) : State :=
  { lengthByteState input i with
    pc := UInt256.ofNat (Artifact.instructionPC 396)
    stack := [UInt256.ofNat i, lengthOffsetWord input, bitLengthWord input,
      UInt256.ofNat input.size, Padding.paddedWord input, UInt256.ofNat 0x62c]
    memory := lengthLoopMemory input (i + 1)
    activeWords := lengthLoopActiveWords input (i + 1) }

def lengthIncrementedState (input : ByteArray) (i : Nat) : State :=
  { lengthStoredState input i with
    pc := UInt256.ofNat (Artifact.instructionPC 401)
    stack := [UInt256.ofNat (i + 1), lengthOffsetWord input,
      bitLengthWord input, UInt256.ofNat input.size, Padding.paddedWord input,
      UInt256.ofNat 0x62c] }

def lengthBackReady (input : ByteArray) (i : Nat) : State :=
  { lengthIncrementedState input i with
    pc := UInt256.ofNat (Artifact.instructionPC 402)
    stack := UInt256.ofNat 0x209 :: (lengthIncrementedState input i).stack }

def lengthBackReturned (input : ByteArray) (i : Nat) : State :=
  { lengthBackReady input i with
    pc := UInt256.ofNat 0x209
    stack := (lengthIncrementedState input i).stack }

private theorem lengthBackReturned_eq (input : ByteArray) (i : Nat) :
    lengthBackReturned input i = lengthLoopState input (i + 1) := by
  unfold lengthBackReturned lengthBackReady lengthIncrementedState
    lengthStoredState lengthByteState lengthBodyState lengthLoopState
    lengthLoopMemory lengthLoopActiveWords
  generalize lengthLoopStart input = s
  cases s
  rfl

@[simp] private theorem lengthBodyState_halt (input : ByteArray) (i : Nat) :
    (lengthBodyState input i).halt = .Running := by rfl

@[simp] private theorem lengthBodyState_pc (input : ByteArray) (i : Nat) :
    (lengthBodyState input i).pc = UInt256.ofNat 0x213 := by rfl

@[simp] private theorem lengthBodyState_memory (input : ByteArray) (i : Nat) :
    (lengthBodyState input i).memory = lengthLoopMemory input i := by rfl

@[simp] private theorem lengthBodyState_activeWords (input : ByteArray) (i : Nat) :
    (lengthBodyState input i).activeWords = lengthLoopActiveWords input i := by rfl

@[simp] private theorem lengthByteState_halt (input : ByteArray) (i : Nat) :
    (lengthByteState input i).halt = .Running := by rfl

@[simp] private theorem lengthByteState_pc (input : ByteArray) (i : Nat) :
    (lengthByteState input i).pc = UInt256.ofNat 0x21c := by rfl

@[simp] private theorem lengthStoredState_halt (input : ByteArray) (i : Nat) :
    (lengthStoredState input i).halt = .Running := by rfl

@[simp] private theorem lengthStoredState_pc (input : ByteArray) (i : Nat) :
    (lengthStoredState input i).pc = UInt256.ofNat 0x220 := by rfl

@[simp] private theorem lengthIncrementedState_halt (input : ByteArray) (i : Nat) :
    (lengthIncrementedState input i).halt = .Running := by rfl

@[simp] private theorem lengthIncrementedState_pc (input : ByteArray) (i : Nat) :
    (lengthIncrementedState input i).pc = UInt256.ofNat 0x226 := by rfl

@[simp] private theorem lengthIncrementedState_stack (input : ByteArray) (i : Nat) :
    (lengthIncrementedState input i).stack =
      [UInt256.ofNat (i + 1), lengthOffsetWord input, bitLengthWord input,
        UInt256.ofNat input.size, Padding.paddedWord input, UInt256.ofNat 0x62c] := by
  rfl

@[simp] private theorem lengthBackReady_halt (input : ByteArray) (i : Nat) :
    (lengthBackReady input i).halt = .Running := by rfl

@[simp] private theorem lengthBackReady_pc (input : ByteArray) (i : Nat) :
    (lengthBackReady input i).pc = UInt256.ofNat 0x229 := by rfl

@[simp] private theorem lengthBackReady_stack (input : ByteArray) (i : Nat) :
    (lengthBackReady input i).stack =
      UInt256.ofNat 0x209 :: (lengthIncrementedState input i).stack := by rfl

@[simp] private theorem lengthBackReady_code (input : ByteArray) (i : Nat) :
    (lengthBackReady input i).executionEnv.code = referenceBytecode := by rfl

@[simp] private theorem validLengthLoop :
    Decode.isValidJumpDest referenceBytecode 0x209 = true := by
  rw [← Artifact.refPc378]
  exact Artifact.referenceArtifact.isValidJumpDest_index 378 (by rfl)

set_option maxHeartbeats 300000 in
private theorem run_lengthCondition (input : ByteArray) (i : Nat) (hi : i < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthConditionPath
      (lengthLoopState input i) = some (lengthBodyState input i) := by
  have hi256 : i < 2 ^ 256 := by omega
  have hiWord : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hi256]
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat 8) = UInt256.ofNat 1 := by
    simp [UInt256.lt, hiWord, Challenge.EvmProof.Word.word_toNat_ofNat, hi]
  have hzero : UInt256.isZero (UInt256.ofNat 1) = (⟨0⟩ : UInt256) := by decide
  simp [lengthConditionPath, lengthIterationPath,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, lengthLoopState, lengthBodyState,
    UInt256.isTrue, hlt, hzero]

set_option maxHeartbeats 300000 in
private theorem run_lengthByte (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthBytePath
      (lengthBodyState input i) = some (lengthByteState input i) := by
  simp [lengthBytePath, lengthIterationPath,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, lengthBodyState, lengthByteState,
    lengthByteWord]

set_option maxHeartbeats 300000 in
private theorem run_lengthStore (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthStorePath
      (lengthByteState input i) = some (lengthStoredState input i) := by
  simp [lengthStorePath, lengthIterationPath,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, lengthByteState, lengthStoredState,
    lengthLoopMemory, lengthLoopActiveWords,
    State.activeWordsAfterUInt256]

set_option maxHeartbeats 300000 in
private theorem run_lengthIncrement (input : ByteArray) (i : Nat) (hi : i < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthIncrementPath
      (lengthStoredState input i) = some (lengthIncrementedState input i) := by
  have hiSucc : i + 1 < 2 ^ 256 := by omega
  have hadd : UInt256.ofNat i + UInt256.ofNat 1 = UInt256.ofNat (i + 1) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat hiSucc
  simp [lengthIncrementPath, lengthIterationPath,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, lengthStoredState, lengthIncrementedState,
    hadd, List.exchange]

set_option maxHeartbeats 200000 in
private theorem run_lengthBackPush (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthBackPushPath
      (lengthIncrementedState input i) = some (lengthBackReady input i) := by
  simp [lengthBackPushPath, lengthBackPath, lengthIterationPath,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, lengthBackReady,
    lengthIncrementedState_stack]

set_option maxHeartbeats 200000 in
private theorem run_lengthBackJump (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthBackJumpPath
      (lengthBackReady input i) = some (lengthBackReturned input i) := by
  change Challenge.EvmProof.Stepper.runLocatedBlock lengthBackJumpPath
      (lengthBackReady input i) = some
        { lengthBackReady input i with
          pc := UInt256.ofNat 0x209
          stack := (lengthIncrementedState input i).stack }
  simp [lengthBackJumpPath, lengthBackPath, lengthIterationPath,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, lengthBackReady_stack]

def gasSteps_lengthIteration (input : ByteArray) (i : Nat) (hi : i < 8) :
    Challenge.EvmProof.GasSteps (lengthLoopState input i)
      (lengthLoopState input (i + 1)) := by
  have g₁ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthConditionPath
    (lengthLoopState_code input i) (lengthLoopState_fork input i)
    (run_lengthCondition input i hi) (lengthLoopState_halt input i) (by rfl)
  have g₂ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthBytePath (by rfl) (by rfl)
    (run_lengthByte input i) (by rfl) (by rfl)
  have g₃ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthStorePath (by rfl) (by rfl)
    (run_lengthStore input i) (by rfl) (by rfl)
  have g₄ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthIncrementPath (by rfl) (by rfl)
    (run_lengthIncrement input i hi) (by rfl) (by rfl)
  have g₅ₐ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthBackPushPath (by rfl) (by rfl)
    (run_lengthBackPush input i) (by rfl) (by rfl)
  have g5raw := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthBackJumpPath (by rfl) (by rfl)
    (run_lengthBackJump input i) (by rfl) (by rfl)
  have g5b := Challenge.EvmProof.GasSteps.cast g5raw rfl
    (lengthBackReturned_eq input i)
  have g₅ := g₅ₐ.trans g5b
  exact g₁.trans (g₂.trans (g₃.trans (g₄.trans g₅)))

def gasSteps_lengthLoop (input : ByteArray) :
    Challenge.EvmProof.GasSteps (lengthLoopState input 0)
      (lengthLoopState input 8) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded (count := 8)
    (I := lengthLoopState input)
    (fun i hi => gasSteps_lengthIteration input i hi)

/-! ## Loop exit and return -/

def padReturned (input : ByteArray) : State :=
  { lengthLoopState input 8 with
    pc := UInt256.ofNat 0x62c
    stack := [Padding.paddedWord input] }

@[simp] theorem padReturned_pc (input : ByteArray) :
    (padReturned input).pc = UInt256.ofNat 0x62c := by rfl

@[simp] theorem padReturned_stack (input : ByteArray) :
    (padReturned input).stack = [Padding.paddedWord input] := by rfl

@[simp] theorem padReturned_halt (input : ByteArray) :
    (padReturned input).halt = .Running := by rfl

@[simp] theorem padReturned_code (input : ByteArray) :
    (padReturned input).executionEnv.code = referenceBytecode := by rfl

@[simp] theorem padReturned_fork (input : ByteArray) :
    (padReturned input).fork = .Osaka := by rfl

@[simp] theorem padReturned_codeAddr (input : ByteArray) :
    (padReturned input).executionEnv.codeAddr = deployAddress := by rfl

@[simp] theorem padReturned_noPrecompile (input : ByteArray) :
    Precompile.isPrecompileWithConfig (padReturned input).executionEnv.precompileConfig (padReturned input).executionEnv.fork
      (padReturned input).executionEnv.codeAddr = false := by
  exact deployAddress_not_precompile

def lengthExitPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨378, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨379, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨380, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨381, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨382, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨383, .push ⟨2, by decide⟩ (UInt256.ofNat 0x22a), by rfl, by decide⟩,
   ⟨384, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨403, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨404, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨405, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨406, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨407, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨408, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨409, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem validLengthExit :
    Decode.isValidJumpDest referenceBytecode 0x22a = true := by
  rw [← Artifact.refPc403]
  exact Artifact.referenceArtifact.isValidJumpDest_index 403 (by rfl)

@[simp] private theorem validPadReturn :
    Decode.isValidJumpDest referenceBytecode 0x62c = true := by
  have hpc : Artifact.referenceArtifact.instructionPC 768 = 0x62c := by rfl
  rw [← hpc]
  exact Artifact.referenceArtifact.isValidJumpDest_index 768 (by rfl)

def lengthExitComparePath := lengthExitPath.take 4
def lengthExitBranchPath := (lengthExitPath.drop 4).take 3
def lengthExitPopPath := (lengthExitPath.drop 7).take 5
def lengthExitReturnPath := lengthExitPath.drop 12
def lengthExitZeroPath := lengthExitBranchPath.take 1
def lengthExitDestPath := (lengthExitBranchPath.drop 1).take 1
def lengthExitJumpToBodyPath := lengthExitBranchPath.drop 2
def lengthExitSwapPath := lengthExitReturnPath.take 1
def lengthExitJumpPath := lengthExitReturnPath.drop 1

def lengthExitComparedState (input : ByteArray) : State :=
  { lengthLoopState input 8 with
    pc := UInt256.ofNat (Artifact.instructionPC 382)
    stack := [⟨0⟩, UInt256.ofNat 8, lengthOffsetWord input,
      bitLengthWord input, UInt256.ofNat input.size, Padding.paddedWord input,
      UInt256.ofNat 0x62c] }

def lengthExitZeroState (input : ByteArray) : State :=
  { lengthExitComparedState input with
    pc := UInt256.ofNat (Artifact.instructionPC 383)
    stack := [UInt256.ofNat 1, UInt256.ofNat 8, lengthOffsetWord input,
      bitLengthWord input, UInt256.ofNat input.size, Padding.paddedWord input,
      UInt256.ofNat 0x62c] }

def lengthExitDestState (input : ByteArray) : State :=
  { lengthExitZeroState input with
    pc := UInt256.ofNat (Artifact.instructionPC 384)
    stack := [UInt256.ofNat 0x22a, UInt256.ofNat 1, UInt256.ofNat 8,
      lengthOffsetWord input, bitLengthWord input, UInt256.ofNat input.size,
      Padding.paddedWord input, UInt256.ofNat 0x62c] }

def lengthExitBodyState (input : ByteArray) : State :=
  { lengthExitDestState input with
    pc := UInt256.ofNat 0x22a
    stack := [UInt256.ofNat 8, lengthOffsetWord input, bitLengthWord input,
      UInt256.ofNat input.size, Padding.paddedWord input, UInt256.ofNat 0x62c] }

def lengthExitPoppedState (input : ByteArray) : State :=
  { lengthExitBodyState input with
    pc := UInt256.ofNat (Artifact.instructionPC 408)
    stack := [Padding.paddedWord input, UInt256.ofNat 0x62c] }

def lengthExitSwapState (input : ByteArray) : State :=
  { lengthExitPoppedState input with
    pc := UInt256.ofNat (Artifact.instructionPC 409)
    stack := [UInt256.ofNat 0x62c, Padding.paddedWord input] }

def padReturnedFromExit (input : ByteArray) : State :=
  { lengthExitSwapState input with
    pc := UInt256.ofNat 0x62c
    stack := [Padding.paddedWord input] }

private theorem padReturnedFromExit_eq (input : ByteArray) :
    padReturnedFromExit input = padReturned input := by
  unfold padReturnedFromExit lengthExitSwapState lengthExitPoppedState
    lengthExitBodyState lengthExitDestState lengthExitZeroState
    lengthExitComparedState padReturned
  generalize lengthLoopState input 8 = s
  cases s
  rfl

@[simp] private theorem lengthExitComparedState_halt (input : ByteArray) :
    (lengthExitComparedState input).halt = .Running := by rfl

@[simp] private theorem lengthExitComparedState_pc (input : ByteArray) :
    (lengthExitComparedState input).pc = UInt256.ofNat 0x20e := by rfl

@[simp] private theorem lengthExitComparedState_pcSucc (input : ByteArray) :
    (lengthExitComparedState input).pc.succ = UInt256.ofNat 0x20f := by
  rw [lengthExitComparedState_pc,
    Challenge.EvmProof.Word.succ_ofNat (by norm_num)]

@[simp] private theorem lengthExitComparedState_stack (input : ByteArray) :
    (lengthExitComparedState input).stack =
      [⟨0⟩, UInt256.ofNat 8, lengthOffsetWord input, bitLengthWord input,
        UInt256.ofNat input.size, Padding.paddedWord input, UInt256.ofNat 0x62c] := by
  rfl

@[simp] private theorem lengthExitComparedState_code (input : ByteArray) :
    (lengthExitComparedState input).executionEnv.code = referenceBytecode := by rfl

@[simp] private theorem lengthExitDestState_halt (input : ByteArray) :
    (lengthExitDestState input).halt = .Running := by rfl

@[simp] private theorem lengthExitDestState_pc (input : ByteArray) :
    (lengthExitDestState input).pc = UInt256.ofNat 0x212 := by rfl

@[simp] private theorem lengthExitDestState_stack (input : ByteArray) :
    (lengthExitDestState input).stack =
      [UInt256.ofNat 0x22a, UInt256.ofNat 1, UInt256.ofNat 8,
        lengthOffsetWord input, bitLengthWord input, UInt256.ofNat input.size,
        Padding.paddedWord input, UInt256.ofNat 0x62c] := by rfl

@[simp] private theorem lengthExitDestState_code (input : ByteArray) :
    (lengthExitDestState input).executionEnv.code = referenceBytecode := by rfl

@[simp] private theorem lengthExitBodyState_halt (input : ByteArray) :
    (lengthExitBodyState input).halt = .Running := by rfl

@[simp] private theorem lengthExitBodyState_pc (input : ByteArray) :
    (lengthExitBodyState input).pc = UInt256.ofNat 0x22a := by rfl

@[simp] private theorem lengthExitPoppedState_halt (input : ByteArray) :
    (lengthExitPoppedState input).halt = .Running := by rfl

@[simp] private theorem lengthExitPoppedState_pc (input : ByteArray) :
    (lengthExitPoppedState input).pc = UInt256.ofNat 0x22f := by rfl

@[simp] private theorem lengthExitPoppedState_stack (input : ByteArray) :
    (lengthExitPoppedState input).stack =
      [Padding.paddedWord input, UInt256.ofNat 0x62c] := by rfl

@[simp] private theorem lengthExitSwapState_halt (input : ByteArray) :
    (lengthExitSwapState input).halt = .Running := by rfl

@[simp] private theorem lengthExitSwapState_pc (input : ByteArray) :
    (lengthExitSwapState input).pc = UInt256.ofNat 0x230 := by rfl

@[simp] private theorem lengthExitSwapState_stack (input : ByteArray) :
    (lengthExitSwapState input).stack =
      [UInt256.ofNat 0x62c, Padding.paddedWord input] := by rfl

@[simp] private theorem lengthExitSwapState_code (input : ByteArray) :
    (lengthExitSwapState input).executionEnv.code = referenceBytecode := by rfl

set_option maxHeartbeats 300000 in
private theorem run_lengthExitCompare (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthExitComparePath
      (lengthLoopState input 8) = some (lengthExitComparedState input) := by
  have hlt : UInt256.lt (UInt256.ofNat 8) (UInt256.ofNat 8) = (⟨0⟩ : UInt256) := by
    decide
  simp [lengthExitComparePath, lengthExitPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthExitComparedState, hlt]

set_option maxHeartbeats 100000 in
private theorem run_lengthExitZero (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthExitZeroPath
      (lengthExitComparedState input) = some (lengthExitZeroState input) := by
  have hzero : UInt256.isZero (UInt256.ofNat 0) = UInt256.ofNat 1 := by decide
  simp [lengthExitZeroPath, lengthExitBranchPath, lengthExitPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthExitZeroState, hzero]

set_option maxHeartbeats 100000 in
private theorem run_lengthExitDest (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthExitDestPath
      (lengthExitZeroState input) = some (lengthExitDestState input) := by
  simp [lengthExitDestPath, lengthExitBranchPath, lengthExitPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthExitZeroState, lengthExitDestState]

set_option maxHeartbeats 100000 in
private theorem run_lengthExitJumpToBody (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthExitJumpToBodyPath
      (lengthExitDestState input) = some (lengthExitBodyState input) := by
  simp [lengthExitJumpToBodyPath, lengthExitBranchPath, lengthExitPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthExitBodyState, UInt256.isTrue]

set_option maxHeartbeats 300000 in
private theorem run_lengthExitPop (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthExitPopPath
      (lengthExitBodyState input) = some (lengthExitPoppedState input) := by
  simp [lengthExitPopPath, lengthExitPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthExitBodyState, lengthExitPoppedState]

set_option maxHeartbeats 200000 in
private theorem run_lengthExitSwap (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthExitSwapPath
      (lengthExitPoppedState input) = some (lengthExitSwapState input) := by
  simp [lengthExitSwapPath, lengthExitReturnPath, lengthExitPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthExitSwapState, List.exchange]

set_option maxHeartbeats 200000 in
private theorem run_lengthExitJump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthExitJumpPath
      (lengthExitSwapState input) = some (padReturnedFromExit input) := by
  change Challenge.EvmProof.Stepper.runLocatedBlock lengthExitJumpPath
      (lengthExitSwapState input) = some
        { lengthExitSwapState input with
          pc := UInt256.ofNat 0x62c
          stack := [Padding.paddedWord input] }
  simp [lengthExitJumpPath, lengthExitReturnPath, lengthExitPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthExitSwapState_stack]

def gasSteps_lengthExit (input : ByteArray) :
    Challenge.EvmProof.GasSteps (lengthLoopState input 8) (padReturned input) := by
  have g₁ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthExitComparePath
    (lengthLoopState_code input 8) (lengthLoopState_fork input 8)
    (run_lengthExitCompare input) (lengthLoopState_halt input 8) (by rfl)
  have g2a := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthExitZeroPath (by rfl) (by rfl)
    (run_lengthExitZero input) (by rfl) (by rfl)
  have g2b := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthExitDestPath (by rfl) (by rfl)
    (run_lengthExitDest input) (by rfl) (by rfl)
  have g2c := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthExitJumpToBodyPath (by rfl) (by rfl)
    (run_lengthExitJumpToBody input) (by rfl) (by rfl)
  have g₂ := g2a.trans (g2b.trans g2c)
  have g₃ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthExitPopPath (by rfl) (by rfl)
    (run_lengthExitPop input) (by rfl) (by rfl)
  have g₄ₐ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthExitSwapPath (by rfl) (by rfl)
    (run_lengthExitSwap input) (by rfl) (by rfl)
  have g4b := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthExitJumpPath (by rfl) (by rfl)
    (run_lengthExitJump input) (by rfl) (by rfl)
  have g₄ := Challenge.EvmProof.GasSteps.cast (g₄ₐ.trans g4b) rfl
    (padReturnedFromExit_eq input)
  exact g₁.trans (g₂.trans (g₃.trans g₄))

/-! ## Bridge from the symbolic trace to canonical RIPEMD-160 padding -/

theorem bitLengthWord_eq (input : ByteArray) (hfit : CalldataFits input) :
    bitLengthWord input = UInt256.ofNat (input.size * 8) := by
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hresult : input.size * 2 ^ 3 < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num at hfit ⊢
    omega
  simpa [bitLengthWord] using
    (Challenge.EvmProof.Word.shiftLeft_ofNat hsize (by decide : 3 < 256) hresult)

theorem lengthByteWord_toNat (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 8) :
    (lengthByteWord input i).toNat = input.size * 8 / 256 ^ i % 256 := by
  have hvalue : input.size * 8 < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num at hfit ⊢
    omega
  have hi256 : i < 2 ^ 256 := by omega
  have hshift : i * 8 < 256 := by omega
  have hshiftResult : i * 2 ^ 3 < 2 ^ 256 := by omega
  have hshiftWord : UInt256.shiftLeft (UInt256.ofNat i)
      (UInt256.ofNat 3) = UInt256.ofNat (i * 8) := by
    simpa using Challenge.EvmProof.Word.shiftLeft_ofNat hi256
      (by decide : 3 < 256) hshiftResult
  rw [lengthByteWord, bitLengthWord_eq input hfit, hshiftWord,
    Challenge.EvmProof.Word.shiftRight_ofNat hvalue hshift]
  simp only [UInt256.land, UInt256.toNat]
  have hland : (↑(Fin.land
      (UInt256.ofNat ((input.size * 8) >>> (i * 8))).val
      (UInt256.ofNat 255).val) : Nat) =
      (UInt256.ofNat ((input.size * 8) >>> (i * 8))).val.val &&&
        (UInt256.ofNat 255).val.val := Fin.and_val _ _
  rw [hland]
  change (UInt256.ofNat ((input.size * 8) >>> (i * 8))).toNat &&&
      (UInt256.ofNat 255).toNat = _
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hvalue)]
  have h255 : (UInt256.ofNat 255).toNat = 255 := by decide
  rw [h255, show 255 = 2 ^ 8 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  rw [show 2 ^ (i * 8) = 256 ^ i by
    rw [Nat.mul_comm, Nat.pow_mul]]

theorem lengthByte_eq (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 8) :
    UInt8.ofNat ((lengthByteWord input i).toNat % 256) =
      (Padding.lengthBytes input)[i]?.getD 0 := by
  rw [lengthByteWord_toNat input hfit i hi]
  rw [Challenge.EvmProof.Memory.getD0_eq_getElem _ _
    (by simpa using hi : i < (Padding.lengthBytes input).size)]
  rw [Padding.lengthByte input i hi]
  congr 1
  rw [show 2 ^ (8 * i) = 256 ^ i by rw [Nat.pow_mul]]
  simp only [Nat.mod_mod]

theorem lengthOffsetWord_eq (input : ByteArray) (hfit : CalldataFits input) :
    lengthOffsetWord input = UInt256.ofNat
      (Padding.messageOffset + Padding.paddedLength input.size - 8) := by
  have hfooter := Padding.input_and_footer_fit input.size
  have hpadded : Padding.paddedLength input.size < 2 ^ 256 := by
    have hlt := Padding.paddedLength_lt input.size
    unfold CalldataFits at hfit
    norm_num at hfit ⊢
    omega
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat
    (a := Padding.paddedLength input.size) (b := 8) (by omega) hpadded
  have hsum : Padding.messageOffset +
      (Padding.paddedLength input.size - 8) < 2 ^ 256 := by
    have hlt := Padding.paddedLength_lt input.size
    unfold CalldataFits at hfit
    norm_num [Padding.messageOffset] at hfit ⊢
    omega
  rw [lengthOffsetWord, Padding.paddedWord_eq input hfit, hsub,
    Challenge.EvmProof.Word.ofNat_add_ofNat hsum]
  congr 1
  omega

theorem lengthOffset_add_toNat (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ 8) :
    (lengthOffsetWord input + UInt256.ofNat i).toNat =
      Padding.messageOffset + Padding.paddedLength input.size - 8 + i := by
  let base := Padding.messageOffset + Padding.paddedLength input.size - 8
  have hbase : base + i < 2 ^ 256 := by
    have hlt := Padding.paddedLength_lt input.size
    unfold CalldataFits at hfit
    dsimp only [base]
    norm_num [Padding.messageOffset] at hfit ⊢
    omega
  rw [lengthOffsetWord_eq input hfit,
    Challenge.EvmProof.Word.ofNat_add_ofNat hbase,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hbase]

def lengthWrittenBytes (input : ByteArray) : Nat → ByteArray
  | 0 => ByteArray.empty
  | i + 1 => lengthWrittenBytes input i ++ ByteArray.mk #[
      (Padding.lengthBytes input)[i]?.getD 0]

@[simp] theorem lengthWrittenBytes_size (input : ByteArray) (i : Nat) :
    (lengthWrittenBytes input i).size = i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [lengthWrittenBytes, ByteArray.size_append, ih]; rfl

theorem lengthLoopMemory_eq (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ 8) :
    lengthLoopMemory input i = MachineState.writeBytes
      (padSentinel input).memory (lengthWrittenBytes input i)
      (Padding.messageOffset + Padding.paddedLength input.size - 8) := by
  induction i with
  | zero => simp [lengthLoopMemory, lengthWrittenBytes, MachineState.writeBytes]
  | succ i ih =>
      have hii : i < 8 := by omega
      rw [lengthLoopMemory, lengthWrittenBytes, lengthByte_eq input hfit i hii,
        lengthOffset_add_toNat input hfit i (by omega), ih (by omega)]
      simpa only [lengthWrittenBytes_size] using
        Challenge.EvmProof.Memory.writeBytes_append_adjacent
          (padSentinel input).memory (lengthWrittenBytes input i)
          (ByteArray.mk #[(Padding.lengthBytes input)[i]?.getD 0])
          (Padding.messageOffset + Padding.paddedLength input.size - 8)

theorem lengthWrittenBytes_getD (input : ByteArray) (i j : Nat) (hj : j < i) :
    (lengthWrittenBytes input i)[j]?.getD 0 =
      (Padding.lengthBytes input)[j]?.getD 0 := by
  induction i with
  | zero => omega
  | succ i ih =>
      rw [lengthWrittenBytes,
        Challenge.EvmProof.Memory.getElem?_getD_append,
        lengthWrittenBytes_size]
      by_cases hji : j < i
      · rw [if_pos hji]
        exact ih hji
      · have hjiEq : j = i := by omega
        subst j
        rw [if_neg (by omega), Nat.sub_self]
        rfl

theorem lengthWrittenBytes_eight (input : ByteArray) :
    lengthWrittenBytes input 8 = Padding.lengthBytes input := by
  apply ByteArray.ext_getElem
  · simp
  · intro i hi₁ hi₂
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₁,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₂]
    exact lengthWrittenBytes_getD input 8 i (by simpa using hi₁)

theorem lengthLoopMemory_eight (input : ByteArray) (hfit : CalldataFits input) :
    lengthLoopMemory input 8 =
      Padding.paddedMemory (padLengthReady input).memory input := by
  rw [lengthLoopMemory_eq input hfit 8 (by omega), lengthWrittenBytes_eight]
  have hsentinel : (padSentinel input).memory =
      Padding.sentinelMemory (padLengthReady input).memory input := by
    simp [padSentinel, padCopied, Padding.sentinelMemory,
      Padding.copiedMemory, Challenge.EvmProof.Memory.readPadded_zero_size]
  rw [hsentinel]
  rfl

/-- Complete certified execution from the challenge initial state through the
RIPEMD-160 padding function. -/
private def gasSteps_padPrefix (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (padLengthReady input) :=
  (Main.gasSteps_initialize input).trans
    ((gasSteps_enterPad input).trans (gasSteps_paddedLength input))

noncomputable def gasSteps_padBody (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (padLengthReady input) (lengthLoopState input 8) :=
  let setup : Challenge.EvmProof.GasSteps (padLengthReady input)
      (lengthLoopState input 0) := Challenge.EvmProof.GasSteps.cast
        (gasSteps_lengthSetup input hfit) rfl (lengthLoopState_zero input).symm
  setup.trans (gasSteps_lengthLoop input)

noncomputable def gasSteps_pad (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (padReturned input) :=
  (gasSteps_padPrefix input).trans
    ((gasSteps_padBody input hfit).trans (gasSteps_lengthExit input))

theorem padReturned_memory (input : ByteArray) (hfit : CalldataFits input) :
    (padReturned input).memory =
      Padding.paddedMemory (padLengthReady input).memory input := by
  exact lengthLoopMemory_eight input hfit

end Challenge.Ripemd160.Reference.Proofs.Bytecode.PaddingTrace
