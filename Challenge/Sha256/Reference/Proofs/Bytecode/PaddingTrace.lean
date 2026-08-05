import Challenge.Sha256.Reference.Proofs.Bytecode.Padding
import Challenge.Sha256.Reference.Proofs.Bytecode.Trace
import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Meter
import YulEvmCompiler.BytesLemmas
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# Direct execution of the reference padding function

The first certified block enters `pad` from the initialized main state.  The
subsequent loop proof uses the two-word function frame established here:
zero output slot above the return destination.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.PaddingTrace

open EvmSemantics
open EvmSemantics.EVM

def pushedReturn (input : ByteArray) : State :=
  { Main.initializedState input with
    pc := (Main.initializedState input).pc + UInt256.ofNat 3
    stack := UInt256.ofNat 1367 :: (Main.initializedState input).stack }

def pushedOutput (input : ByteArray) : State :=
  { pushedReturn input with
    pc := (pushedReturn input).pc.succ
    stack := ⟨0⟩ :: (pushedReturn input).stack }

def pushedPad (input : ByteArray) : State :=
  { pushedOutput input with
    pc := (pushedOutput input).pc + UInt256.ofNat 3
    stack := UInt256.ofNat 357 :: (pushedOutput input).stack }

def padEntry (input : ByteArray) : State :=
  { pushedPad input with
    pc := UInt256.ofNat 357
    stack := [⟨0⟩, UInt256.ofNat 1367] }

def padBodyStart (input : ByteArray) : State :=
  { padEntry input with pc := (padEntry input).pc.succ }

def padSized (input : ByteArray) : State :=
  { padBodyStart input with
    pc := (padBodyStart input).pc.succ
    stack := UInt256.ofNat input.size :: (padBodyStart input).stack }

private def p262 (input : ByteArray) : State :=
  { padSized input with
    pc := (padSized input).pc + UInt256.ofNat 2
    stack := UInt256.ofNat 72 :: (padSized input).stack }

private def p263 (input : ByteArray) : State :=
  { p262 input with
    pc := (p262 input).pc.succ
    stack := UInt256.ofNat input.size :: (p262 input).stack }

private def p264 (input : ByteArray) : State :=
  { p263 input with
    pc := (p263 input).pc.succ
    stack := (UInt256.ofNat input.size + UInt256.ofNat 72) ::
      (padSized input).stack }

private def p265 (input : ByteArray) : State :=
  { p264 input with
    pc := (p264 input).pc + UInt256.ofNat 2
    stack := UInt256.ofNat 6 :: (p264 input).stack }

private def p266 (input : ByteArray) : State :=
  { p265 input with
    pc := (p265 input).pc.succ
    stack := UInt256.shiftRight
      (UInt256.ofNat input.size + UInt256.ofNat 72) (UInt256.ofNat 6) ::
      (padSized input).stack }

private def p267 (input : ByteArray) : State :=
  { p266 input with
    pc := (p266 input).pc + UInt256.ofNat 2
    stack := UInt256.ofNat 6 :: (p266 input).stack }

private def p268 (input : ByteArray) : State :=
  { p267 input with
    pc := (p267 input).pc.succ
    stack := Padding.paddedWord input :: (padSized input).stack }

private def p269 (input : ByteArray) : State :=
  { p268 input with
    pc := (p268 input).pc.succ
    stack := [⟨0⟩, UInt256.ofNat input.size, Padding.paddedWord input,
      UInt256.ofNat 1367] }

def padLengthReady (input : ByteArray) : State :=
  { p269 input with
    pc := (p269 input).pc.succ
    stack := [UInt256.ofNat input.size, Padding.paddedWord input,
      UInt256.ofNat 1367] }

def bitLengthWord (input : ByteArray) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat input.size) (UInt256.ofNat 3)

def lengthOffsetWord (input : ByteArray) : UInt256 :=
  UInt256.ofNat Padding.messageOffset +
    (Padding.paddedWord input - UInt256.ofNat 8)

def padCopied (input : ByteArray) : State :=
  { padLengthReady input with
    memory := MachineState.writeBytes (padLengthReady input).memory
      (MachineState.readPadded input 0 input.size) Padding.messageOffset
    activeWords := (padLengthReady input).activeWordsAfterUInt256
      Padding.messageOffset input.size }

def padSentinel (input : ByteArray) : State :=
  { padCopied input with
    memory := MachineState.writeBytes (padCopied input).memory
      (ByteArray.mk #[0x80]) (Padding.messageOffset + input.size)
    activeWords := (padCopied input).activeWordsAfterUInt256
      (Padding.messageOffset + input.size) 1 }

/-- Entry to the fixed eight-iteration loop that stores the big-endian bit
length.  The calldata bytes and the `0x80` sentinel are already in memory. -/
def lengthLoopStart (input : ByteArray) : State :=
  { padSentinel input with
    pc := UInt256.ofNat (Artifact.instructionPC 289)
    stack := [⟨0⟩, lengthOffsetWord input, bitLengthWord input,
      UInt256.ofNat input.size, Padding.paddedWord input, UInt256.ofNat 1367] }

def lengthSetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨270, .op (.Dup ⟨0, by decide⟩), by rfl,
      ⟨by decide, trivial, rfl⟩⟩,
   ⟨271, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨272, .push ⟨2, by decide⟩ (UInt256.ofNat Padding.messageOffset),
      by rfl, by decide⟩,
   ⟨273, .op .CALLDATACOPY, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨274, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨275, .op (.Dup ⟨1, by decide⟩), by rfl,
      ⟨by decide, trivial, rfl⟩⟩,
   ⟨276, .push ⟨2, by decide⟩ (UInt256.ofNat Padding.messageOffset),
      by rfl, by decide⟩,
   ⟨277, .op .ADD, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨278, .op .MSTORE8, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨279, .op (.Dup ⟨0, by decide⟩), by rfl,
      ⟨by decide, trivial, rfl⟩⟩,
   ⟨280, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨281, .op .SHL, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨282, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨283, .op (.Dup ⟨3, by decide⟩), by rfl,
      ⟨by decide, trivial, rfl⟩⟩,
   ⟨284, .op .SUB, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨285, .push ⟨2, by decide⟩ (UInt256.ofNat Padding.messageOffset),
      by rfl, by decide⟩,
   ⟨286, .op .ADD, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨287, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨288, .op .JUMPDEST, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def lengthByteWord (input : ByteArray) (i : Nat) : UInt256 :=
  UInt256.land
    (UInt256.shiftRight (bitLengthWord input)
      (UInt256.shiftLeft (UInt256.ofNat 7 - UInt256.ofNat i)
        (UInt256.ofNat 3)))
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
    pc := UInt256.ofNat (Artifact.instructionPC 289)
    stack := [UInt256.ofNat i, lengthOffsetWord input, bitLengthWord input,
      UInt256.ofNat input.size, Padding.paddedWord input, UInt256.ofNat 1367]
    memory := lengthLoopMemory input i
    activeWords := lengthLoopActiveWords input i }

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def computePaddedLength261 :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨261, .push ⟨1, by decide⟩ (UInt256.ofNat 72), by rfl, by decide⟩
def computePaddedLength262 :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨262, .op (.Dup ⟨1, by decide⟩), by rfl,
    wfOp (by decide) trivial rfl⟩
def computePaddedLength263 :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨263, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩
def computePaddedLength264 :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨264, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩
def computePaddedLength265 :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨265, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩
def computePaddedLength266 :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨266, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩
def computePaddedLength267 :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨267, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩
def computePaddedLength268 :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨268, .op (.Swap ⟨1, by decide⟩), by rfl,
    wfOp (by decide) trivial rfl⟩
def computePaddedLength269 :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨269, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩

/-- The straight-line arithmetic block which rounds `input.size + 72` up to
the next 64-byte boundary.  This path is also the reusable executable seam for
gas metering and participant bytecode equivalence proofs. -/
def computePaddedLengthPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [computePaddedLength261, computePaddedLength262, computePaddedLength263,
   computePaddedLength264, computePaddedLength265, computePaddedLength266,
   computePaddedLength267, computePaddedLength268, computePaddedLength269]

@[simp] private theorem refPc261 :
    Artifact.referenceArtifact.instructionPC 261 = 359 := by decide
@[simp] private theorem refPc262 :
    Artifact.referenceArtifact.instructionPC 262 = 361 := by decide
@[simp] private theorem refPc263 :
    Artifact.referenceArtifact.instructionPC 263 = 362 := by decide
@[simp] private theorem refPc264 :
    Artifact.referenceArtifact.instructionPC 264 = 363 := by decide
@[simp] private theorem refPc265 :
    Artifact.referenceArtifact.instructionPC 265 = 365 := by decide
@[simp] private theorem refPc266 :
    Artifact.referenceArtifact.instructionPC 266 = 366 := by decide
@[simp] private theorem refPc267 :
    Artifact.referenceArtifact.instructionPC 267 = 368 := by decide
@[simp] private theorem refPc268 :
    Artifact.referenceArtifact.instructionPC 268 = 369 := by decide
@[simp] private theorem refPc269 :
    Artifact.referenceArtifact.instructionPC 269 = 370 := by decide

@[simp] private theorem padSized_pcToNat (input : ByteArray) :
    (padSized input).pc.toNat = 359 := by rfl
@[simp] private theorem p262_pcToNat (input : ByteArray) :
    (p262 input).pc.toNat = 361 := by rfl
@[simp] private theorem p263_pcToNat (input : ByteArray) :
    (p263 input).pc.toNat = 362 := by rfl
@[simp] private theorem p264_pcToNat (input : ByteArray) :
    (p264 input).pc.toNat = 363 := by rfl
@[simp] private theorem p265_pcToNat (input : ByteArray) :
    (p265 input).pc.toNat = 365 := by rfl
@[simp] private theorem p266_pcToNat (input : ByteArray) :
    (p266 input).pc.toNat = 366 := by rfl
@[simp] private theorem p267_pcToNat (input : ByteArray) :
    (p267 input).pc.toNat = 368 := by rfl
@[simp] private theorem p268_pcToNat (input : ByteArray) :
    (p268 input).pc.toNat = 369 := by rfl
@[simp] private theorem p269_pcToNat (input : ByteArray) :
    (p269 input).pc.toNat = 370 := by rfl
@[simp] private theorem padSized_stack (input : ByteArray) :
    (padSized input).stack =
      [UInt256.ofNat input.size, ⟨0⟩, UInt256.ofNat 1367] := by rfl
@[simp] private theorem p262_stack (input : ByteArray) :
    (p262 input).stack =
      [UInt256.ofNat 72, UInt256.ofNat input.size, ⟨0⟩,
        UInt256.ofNat 1367] := by rfl
@[simp] private theorem p263_stack (input : ByteArray) :
    (p263 input).stack =
      [UInt256.ofNat input.size, UInt256.ofNat 72,
        UInt256.ofNat input.size, ⟨0⟩, UInt256.ofNat 1367] := by rfl
@[simp] private theorem p264_stack (input : ByteArray) :
    (p264 input).stack =
      [UInt256.ofNat input.size + UInt256.ofNat 72,
        UInt256.ofNat input.size, ⟨0⟩, UInt256.ofNat 1367] := by rfl
@[simp] private theorem p265_stack (input : ByteArray) :
    (p265 input).stack =
      [UInt256.ofNat 6,
        UInt256.ofNat input.size + UInt256.ofNat 72,
        UInt256.ofNat input.size, ⟨0⟩, UInt256.ofNat 1367] := by rfl
@[simp] private theorem p266_stack (input : ByteArray) :
    (p266 input).stack =
      [UInt256.shiftRight
          (UInt256.ofNat input.size + UInt256.ofNat 72) (UInt256.ofNat 6),
        UInt256.ofNat input.size, ⟨0⟩, UInt256.ofNat 1367] := by rfl
@[simp] private theorem p267_stack (input : ByteArray) :
    (p267 input).stack =
      [UInt256.ofNat 6,
        UInt256.shiftRight
          (UInt256.ofNat input.size + UInt256.ofNat 72) (UInt256.ofNat 6),
        UInt256.ofNat input.size, ⟨0⟩, UInt256.ofNat 1367] := by rfl
@[simp] private theorem p268_stack (input : ByteArray) :
    (p268 input).stack =
      [Padding.paddedWord input, UInt256.ofNat input.size, ⟨0⟩,
        UInt256.ofNat 1367] := by rfl
@[simp] private theorem p269_stack (input : ByteArray) :
    (p269 input).stack =
      [⟨0⟩, UInt256.ofNat input.size, Padding.paddedWord input,
        UInt256.ofNat 1367] := by rfl

def lengthIterationPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨289, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨290, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨291, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨292, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨293, .push ⟨2, by decide⟩ (UInt256.ofNat 434), by rfl, by decide⟩,
   ⟨294, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨295, .push ⟨1, by decide⟩ (UInt256.ofNat 255), by rfl, by decide⟩,
   ⟨296, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨297, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨298, .push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨299, .op .SUB, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨300, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨301, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨302, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨303, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨304, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨305, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨306, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨307, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨308, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨309, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨310, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨311, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨312, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨313, .push ⟨2, by decide⟩ (UInt256.ofNat 398), by rfl, by decide⟩,
   ⟨314, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨288, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem padLengthReady_halt (input : ByteArray) :
    (padLengthReady input).halt = .Running := by rfl

@[simp] private theorem padLengthReady_fork (input : ByteArray) :
    (padLengthReady input).fork = .Osaka := by rfl

@[simp] private theorem padLengthReady_pcToNat (input : ByteArray) :
    (padLengthReady input).pc.toNat = Artifact.instructionPC 270 := by rfl

@[simp] private theorem padLengthReady_pc (input : ByteArray) :
    (padLengthReady input).pc = UInt256.ofNat (Artifact.instructionPC 270) := by
  rfl

@[simp] private theorem padLengthReady_stack (input : ByteArray) :
    (padLengthReady input).stack =
      [UInt256.ofNat input.size, Padding.paddedWord input,
        UInt256.ofNat 1367] := by rfl

@[simp] private theorem padLengthReady_calldata (input : ByteArray) :
    (padLengthReady input).executionEnv.calldata = input := by rfl

@[simp] private theorem pc270 : Artifact.instructionPC 270 = 371 := by decide
@[simp] private theorem pc271 : Artifact.instructionPC 271 = 372 := by decide
@[simp] private theorem pc272 : Artifact.instructionPC 272 = 373 := by decide
@[simp] private theorem pc273 : Artifact.instructionPC 273 = 376 := by decide
@[simp] private theorem pc274 : Artifact.instructionPC 274 = 377 := by decide
@[simp] private theorem pc275 : Artifact.instructionPC 275 = 379 := by decide
@[simp] private theorem pc276 : Artifact.instructionPC 276 = 380 := by decide
@[simp] private theorem pc277 : Artifact.instructionPC 277 = 383 := by decide
@[simp] private theorem pc278 : Artifact.instructionPC 278 = 384 := by decide
@[simp] private theorem pc279 : Artifact.instructionPC 279 = 385 := by decide
@[simp] private theorem pc280 : Artifact.instructionPC 280 = 386 := by decide
@[simp] private theorem pc281 : Artifact.instructionPC 281 = 388 := by decide
@[simp] private theorem pc282 : Artifact.instructionPC 282 = 389 := by decide
@[simp] private theorem pc283 : Artifact.instructionPC 283 = 391 := by decide
@[simp] private theorem pc284 : Artifact.instructionPC 284 = 392 := by decide
@[simp] private theorem pc285 : Artifact.instructionPC 285 = 393 := by decide
@[simp] private theorem pc286 : Artifact.instructionPC 286 = 396 := by decide
@[simp] private theorem pc287 : Artifact.instructionPC 287 = 397 := by decide
@[simp] private theorem pc288 : Artifact.instructionPC 288 = 398 := by decide
@[simp] private theorem pc289 : Artifact.instructionPC 289 = 399 := by decide

@[simp] private theorem refPc270 :
    Artifact.referenceArtifact.instructionPC 270 = 371 := by decide
@[simp] private theorem refPc271 :
    Artifact.referenceArtifact.instructionPC 271 = 372 := by decide
@[simp] private theorem refPc272 :
    Artifact.referenceArtifact.instructionPC 272 = 373 := by decide
@[simp] private theorem refPc273 :
    Artifact.referenceArtifact.instructionPC 273 = 376 := by decide
@[simp] private theorem refPc274 :
    Artifact.referenceArtifact.instructionPC 274 = 377 := by decide
@[simp] private theorem refPc275 :
    Artifact.referenceArtifact.instructionPC 275 = 379 := by decide
@[simp] private theorem refPc276 :
    Artifact.referenceArtifact.instructionPC 276 = 380 := by decide
@[simp] private theorem refPc277 :
    Artifact.referenceArtifact.instructionPC 277 = 383 := by decide
@[simp] private theorem refPc278 :
    Artifact.referenceArtifact.instructionPC 278 = 384 := by decide
@[simp] private theorem refPc279 :
    Artifact.referenceArtifact.instructionPC 279 = 385 := by decide
@[simp] private theorem refPc280 :
    Artifact.referenceArtifact.instructionPC 280 = 386 := by decide
@[simp] private theorem refPc281 :
    Artifact.referenceArtifact.instructionPC 281 = 388 := by decide
@[simp] private theorem refPc282 :
    Artifact.referenceArtifact.instructionPC 282 = 389 := by decide
@[simp] private theorem refPc283 :
    Artifact.referenceArtifact.instructionPC 283 = 391 := by decide
@[simp] private theorem refPc284 :
    Artifact.referenceArtifact.instructionPC 284 = 392 := by decide
@[simp] private theorem refPc285 :
    Artifact.referenceArtifact.instructionPC 285 = 393 := by decide
@[simp] private theorem refPc286 :
    Artifact.referenceArtifact.instructionPC 286 = 396 := by decide
@[simp] private theorem refPc287 :
    Artifact.referenceArtifact.instructionPC 287 = 397 := by decide
@[simp] private theorem refPc288 :
    Artifact.referenceArtifact.instructionPC 288 = 398 := by decide

@[simp] private theorem next270 : (UInt256.ofNat 371).succ = UInt256.ofNat 372 := by decide
@[simp] private theorem next271 : (UInt256.ofNat 372).succ = UInt256.ofNat 373 := by decide
@[simp] private theorem next272 : UInt256.ofNat 373 + UInt256.ofNat 3 = UInt256.ofNat 376 := by decide
@[simp] private theorem next273 : (UInt256.ofNat 376).succ = UInt256.ofNat 377 := by decide
@[simp] private theorem next274 : UInt256.ofNat 377 + UInt256.ofNat 2 = UInt256.ofNat 379 := by decide
@[simp] private theorem next275 : (UInt256.ofNat 379).succ = UInt256.ofNat 380 := by decide
@[simp] private theorem next276 : UInt256.ofNat 380 + UInt256.ofNat 3 = UInt256.ofNat 383 := by decide
@[simp] private theorem next277 : (UInt256.ofNat 383).succ = UInt256.ofNat 384 := by decide
@[simp] private theorem next278 : (UInt256.ofNat 384).succ = UInt256.ofNat 385 := by decide
@[simp] private theorem next279 : (UInt256.ofNat 385).succ = UInt256.ofNat 386 := by decide
@[simp] private theorem next280 : UInt256.ofNat 386 + UInt256.ofNat 2 = UInt256.ofNat 388 := by decide
@[simp] private theorem next281 : (UInt256.ofNat 388).succ = UInt256.ofNat 389 := by decide
@[simp] private theorem next282 : UInt256.ofNat 389 + UInt256.ofNat 2 = UInt256.ofNat 391 := by decide
@[simp] private theorem next283 : (UInt256.ofNat 391).succ = UInt256.ofNat 392 := by decide
@[simp] private theorem next284 : (UInt256.ofNat 392).succ = UInt256.ofNat 393 := by decide
@[simp] private theorem next285 : UInt256.ofNat 393 + UInt256.ofNat 3 = UInt256.ofNat 396 := by decide
@[simp] private theorem next286 : (UInt256.ofNat 396).succ = UInt256.ofNat 397 := by decide
@[simp] private theorem next287 : (UInt256.ofNat 397).succ = UInt256.ofNat 398 := by decide
@[simp] private theorem next288 : (UInt256.ofNat 398).succ = UInt256.ofNat 399 := by decide

@[simp] private theorem refPc289 : Artifact.referenceArtifact.instructionPC 289 = 399 := by decide
@[simp] private theorem refPc290 : Artifact.referenceArtifact.instructionPC 290 = 401 := by decide
@[simp] private theorem refPc291 : Artifact.referenceArtifact.instructionPC 291 = 402 := by decide
@[simp] private theorem refPc292 : Artifact.referenceArtifact.instructionPC 292 = 403 := by decide
@[simp] private theorem refPc293 : Artifact.referenceArtifact.instructionPC 293 = 404 := by decide
@[simp] private theorem refPc294 : Artifact.referenceArtifact.instructionPC 294 = 407 := by decide
@[simp] private theorem refPc295 : Artifact.referenceArtifact.instructionPC 295 = 408 := by decide
@[simp] private theorem refPc296 : Artifact.referenceArtifact.instructionPC 296 = 410 := by decide
@[simp] private theorem refPc297 : Artifact.referenceArtifact.instructionPC 297 = 411 := by decide
@[simp] private theorem refPc298 : Artifact.referenceArtifact.instructionPC 298 = 412 := by decide
@[simp] private theorem refPc299 : Artifact.referenceArtifact.instructionPC 299 = 414 := by decide
@[simp] private theorem refPc300 : Artifact.referenceArtifact.instructionPC 300 = 415 := by decide
@[simp] private theorem refPc301 : Artifact.referenceArtifact.instructionPC 301 = 417 := by decide
@[simp] private theorem refPc302 : Artifact.referenceArtifact.instructionPC 302 = 418 := by decide
@[simp] private theorem refPc303 : Artifact.referenceArtifact.instructionPC 303 = 419 := by decide
@[simp] private theorem refPc304 : Artifact.referenceArtifact.instructionPC 304 = 420 := by decide
@[simp] private theorem refPc305 : Artifact.referenceArtifact.instructionPC 305 = 421 := by decide
@[simp] private theorem refPc306 : Artifact.referenceArtifact.instructionPC 306 = 422 := by decide
@[simp] private theorem refPc307 : Artifact.referenceArtifact.instructionPC 307 = 423 := by decide
@[simp] private theorem refPc308 : Artifact.referenceArtifact.instructionPC 308 = 424 := by decide
@[simp] private theorem refPc309 : Artifact.referenceArtifact.instructionPC 309 = 426 := by decide
@[simp] private theorem refPc310 : Artifact.referenceArtifact.instructionPC 310 = 427 := by decide
@[simp] private theorem refPc311 : Artifact.referenceArtifact.instructionPC 311 = 428 := by decide
@[simp] private theorem refPc312 : Artifact.referenceArtifact.instructionPC 312 = 429 := by decide
@[simp] private theorem refPc313 : Artifact.referenceArtifact.instructionPC 313 = 430 := by decide
@[simp] private theorem refPc314 : Artifact.referenceArtifact.instructionPC 314 = 433 := by decide
@[simp] private theorem refPc315 : Artifact.referenceArtifact.instructionPC 315 = 434 := by decide

@[simp] private theorem next289 : UInt256.ofNat 399 + UInt256.ofNat 2 = UInt256.ofNat 401 := by decide
@[simp] private theorem next290 : (UInt256.ofNat 401).succ = UInt256.ofNat 402 := by decide
@[simp] private theorem next291 : (UInt256.ofNat 402).succ = UInt256.ofNat 403 := by decide
@[simp] private theorem next292 : (UInt256.ofNat 403).succ = UInt256.ofNat 404 := by decide
@[simp] private theorem next293 : UInt256.ofNat 404 + UInt256.ofNat 3 = UInt256.ofNat 407 := by decide
@[simp] private theorem next294 : (UInt256.ofNat 407).succ = UInt256.ofNat 408 := by decide
@[simp] private theorem next295 : UInt256.ofNat 408 + UInt256.ofNat 2 = UInt256.ofNat 410 := by decide
@[simp] private theorem next296 : (UInt256.ofNat 410).succ = UInt256.ofNat 411 := by decide
@[simp] private theorem next297 : (UInt256.ofNat 411).succ = UInt256.ofNat 412 := by decide
@[simp] private theorem next298 : UInt256.ofNat 412 + UInt256.ofNat 2 = UInt256.ofNat 414 := by decide
@[simp] private theorem next299 : (UInt256.ofNat 414).succ = UInt256.ofNat 415 := by decide
@[simp] private theorem next300 : UInt256.ofNat 415 + UInt256.ofNat 2 = UInt256.ofNat 417 := by decide
@[simp] private theorem next301 : (UInt256.ofNat 417).succ = UInt256.ofNat 418 := by decide
@[simp] private theorem next302 : (UInt256.ofNat 418).succ = UInt256.ofNat 419 := by decide
@[simp] private theorem next303 : (UInt256.ofNat 419).succ = UInt256.ofNat 420 := by decide
@[simp] private theorem next304 : (UInt256.ofNat 420).succ = UInt256.ofNat 421 := by decide
@[simp] private theorem next305 : (UInt256.ofNat 421).succ = UInt256.ofNat 422 := by decide
@[simp] private theorem next306 : (UInt256.ofNat 422).succ = UInt256.ofNat 423 := by decide
@[simp] private theorem next307 : (UInt256.ofNat 423).succ = UInt256.ofNat 424 := by decide
@[simp] private theorem next308 : UInt256.ofNat 424 + UInt256.ofNat 2 = UInt256.ofNat 426 := by decide
@[simp] private theorem next309 : (UInt256.ofNat 426).succ = UInt256.ofNat 427 := by decide
@[simp] private theorem next310 : (UInt256.ofNat 427).succ = UInt256.ofNat 428 := by decide
@[simp] private theorem next311 : (UInt256.ofNat 428).succ = UInt256.ofNat 429 := by decide
@[simp] private theorem next312 : (UInt256.ofNat 429).succ = UInt256.ofNat 430 := by decide
@[simp] private theorem next313 : UInt256.ofNat 430 + UInt256.ofNat 3 = UInt256.ofNat 433 := by decide

@[simp] private theorem valid398 :
    Decode.isValidJumpDest referenceBytecode 398 = true := by
  simpa using Artifact.isValidJumpDest_index 288 (by rfl)

def gasSteps_enterPad (input : ByteArray) :
    Challenge.EvmProof.GasSteps (Main.initializedState input) (padEntry input) := by
  have hinitPC : (Main.initializedState input).pc =
      UInt256.ofNat (Artifact.instructionPC 707) := by rfl
  have hinitStack : (Main.initializedState input).stack = [] := by rfl
  have hreturnPC : (pushedReturn input).pc =
      UInt256.ofNat (Artifact.instructionPC 708) := by
    rw [pushedReturn, hinitPC]
    exact Trace.pushPC (index := 707) (width := 2) (by decide)
  have houtputPC : (pushedOutput input).pc =
      UInt256.ofNat (Artifact.instructionPC 709) := by
    rw [pushedOutput, hreturnPC]
    exact Trace.succPC (index := 708) (by decide)
  have hpadPC : (pushedPad input).pc =
      UInt256.ofNat (Artifact.instructionPC 710) := by
    rw [pushedPad, houtputPC]
    exact Trace.pushPC (index := 709) (width := 2) (by decide)
  have hpushReturn : Challenge.EvmProof.GasSteps
      (Main.initializedState input) (pushedReturn input) := by
    have hdecode := Trace.decodedPushAt (Main.initializedState input) 707
      ⟨2, by decide⟩ (UInt256.ofNat 1367) rfl rfl rfl (by decide)
      (by rfl)
    have hstep := Challenge.EvmProof.GasStep.pushN
      (s := Main.initializedState input) ⟨2, by decide⟩
      (UInt256.ofNat 1367) 2 (by decide) hdecode (by simp [hinitStack])
      (by rfl) (by rfl)
    simpa [pushedReturn] using hstep
  have hpushOutput : Challenge.EvmProof.GasSteps
      (pushedReturn input) (pushedOutput input) := by
    have hdecode := Trace.decodedPushOpAt (pushedReturn input) 708
      ⟨0, by decide⟩ ⟨0⟩ rfl (by
        exact hreturnPC) rfl
        (by decide) (by rfl)
    have hstep := Challenge.EvmProof.GasStep.push0 (s := pushedReturn input)
      hdecode (by simp [pushedReturn, hinitStack]) (by rfl) (by rfl)
    simpa [pushedOutput] using hstep
  have hpushPad : Challenge.EvmProof.GasSteps
      (pushedOutput input) (pushedPad input) := by
    have hdecode := Trace.decodedPushAt (pushedOutput input) 709
      ⟨2, by decide⟩ (UInt256.ofNat 357) rfl (by
        exact houtputPC) rfl
        (by decide) (by rfl)
    have hstep := Challenge.EvmProof.GasStep.pushN
      (s := pushedOutput input) ⟨2, by decide⟩
      (UInt256.ofNat 357) 2 (by decide) hdecode
      (by simp [pushedOutput, pushedReturn, hinitStack])
      (by rfl) (by rfl)
    simpa [pushedPad] using hstep
  have hjump : Challenge.EvmProof.GasSteps (pushedPad input) (padEntry input) := by
    have hdecode := Trace.decodedOpAt (pushedPad input) 710 .JUMP rfl hpadPC rfl
      (by decide) trivial (by rfl)
    have hvalid : Decode.isValidJumpDest
        (pushedPad input).executionEnv.code (UInt256.ofNat 357).toNat = true := by
      change Decode.isValidJumpDest referenceBytecode 357 = true
      have hv := Trace.validJumpDestAt 259 rfl
      change Decode.isValidJumpDest referenceBytecode
        (Artifact.instructionPC 259 % 2 ^ 256) = true at hv
      rw [show Artifact.instructionPC 259 % 2 ^ 256 = 357 by decide] at hv
      exact hv
    have hstep := Challenge.EvmProof.GasStep.jump (s := pushedPad input)
      (UInt256.ofNat 357) [⟨0⟩, UInt256.ofNat 1367] hdecode (by rfl) hvalid
      (by simp [pushedPad, pushedOutput, pushedReturn, hinitStack,
        Operation.pushArity, Operation.popArity])
      (by rfl) (by rfl)
    simpa [padEntry] using hstep
  exact hpushReturn.trans (hpushOutput.trans (hpushPad.trans hjump))

def gasSteps_padReadSize (input : ByteArray) :
    Challenge.EvmProof.GasSteps (padEntry input) (padSized input) := by
  have hentryPC : (padEntry input).pc =
      UInt256.ofNat (Artifact.instructionPC 259) := by
    rw [padEntry]
    congr 1
  have hbodyPC : (padBodyStart input).pc =
      UInt256.ofNat (Artifact.instructionPC 260) := by
    rw [padBodyStart, hentryPC]
    exact Trace.succPC (index := 259) (by decide)
  have gjumpdest : Challenge.EvmProof.GasSteps
      (padEntry input) (padBodyStart input) := by
    have hdecode := Trace.decodedOpAt (padEntry input) 259 .JUMPDEST rfl
      hentryPC rfl (by decide) trivial (by rfl)
    have hstep := Challenge.EvmProof.GasStep.jumpdest (s := padEntry input)
      hdecode (by simp [padEntry, pushedPad, pushedOutput, pushedReturn,
        Operation.pushArity, Operation.popArity]) (by rfl) (by rfl)
    simpa [padBodyStart] using hstep
  have gsize : Challenge.EvmProof.GasSteps
      (padBodyStart input) (padSized input) := by
    have hcalldata : (padBodyStart input).executionEnv.calldata = input := by rfl
    have hdecode := Trace.decodedOpAt (padBodyStart input) 260 .CALLDATASIZE
      rfl hbodyPC rfl (by decide) trivial (by rfl)
    have hstep := Challenge.EvmProof.GasStep.calldatasize (s := padBodyStart input)
      hdecode (by simp [padBodyStart, padEntry, pushedPad, pushedOutput,
        pushedReturn]) (by rfl) (by rfl)
    simpa [padSized, hcalldata] using hstep
  exact gjumpdest.trans gsize

private def gasSteps_computePaddedLength_manual (input : ByteArray) :
    Challenge.EvmProof.GasSteps (padSized input) (padLengthReady input) := by
  have hinitStack : (Main.initializedState input).stack = [] := by rfl
  have hbodyStack : (padBodyStart input).stack =
      [⟨0⟩, UInt256.ofNat 1367] := by rfl
  have hentryPC : (padEntry input).pc =
      UInt256.ofNat (Artifact.instructionPC 259) := by
    rw [padEntry]
    congr 1
  have hbodyPC : (padBodyStart input).pc =
      UInt256.ofNat (Artifact.instructionPC 260) := by
    rw [padBodyStart, hentryPC]
    exact Trace.succPC (index := 259) (by decide)
  have h261 : (padSized input).pc =
      UInt256.ofNat (Artifact.instructionPC 261) := by
    rw [padSized, hbodyPC]
    exact Trace.succPC (index := 260) (by decide)
  have h262 : (p262 input).pc = UInt256.ofNat (Artifact.instructionPC 262) := by
    rw [p262, h261]
    exact Trace.pushPC (index := 261) (width := 1) (by decide)
  have h263 : (p263 input).pc = UInt256.ofNat (Artifact.instructionPC 263) := by
    rw [p263, h262]
    exact Trace.succPC (index := 262) (by decide)
  have h264 : (p264 input).pc = UInt256.ofNat (Artifact.instructionPC 264) := by
    rw [p264, h263]
    exact Trace.succPC (index := 263) (by decide)
  have h265 : (p265 input).pc = UInt256.ofNat (Artifact.instructionPC 265) := by
    rw [p265, h264]
    exact Trace.pushPC (index := 264) (width := 1) (by decide)
  have h266 : (p266 input).pc = UInt256.ofNat (Artifact.instructionPC 266) := by
    rw [p266, h265]
    exact Trace.succPC (index := 265) (by decide)
  have h267 : (p267 input).pc = UInt256.ofNat (Artifact.instructionPC 267) := by
    rw [p267, h266]
    exact Trace.pushPC (index := 266) (width := 1) (by decide)
  have h268 : (p268 input).pc = UInt256.ofNat (Artifact.instructionPC 268) := by
    rw [p268, h267]
    exact Trace.succPC (index := 267) (by decide)
  have h269 : (p269 input).pc = UInt256.ofNat (Artifact.instructionPC 269) := by
    rw [p269, h268]
    exact Trace.succPC (index := 268) (by decide)
  have g261 : Challenge.EvmProof.GasSteps (padSized input) (p262 input) := by
    have hd := Trace.decodedPushAt (padSized input) 261 ⟨1, by decide⟩
      (UInt256.ofNat 72) rfl h261 rfl (by decide) (by rfl)
    have g := Challenge.EvmProof.GasStep.pushN (s := padSized input)
      ⟨1, by decide⟩ (UInt256.ofNat 72) 1 (by decide) hd
      (by simp [padSized, padBodyStart, padEntry, pushedPad, pushedOutput,
        pushedReturn, hinitStack]) (by rfl) (by rfl)
    simpa [p262] using g
  have g262 : Challenge.EvmProof.GasSteps (p262 input) (p263 input) := by
    have hd := Trace.decodedOpAt (p262 input) 262 (.Dup ⟨1, by decide⟩)
      rfl h262 rfl (by decide) trivial (by rfl)
    have g := Challenge.EvmProof.GasStep.dup (s := p262 input) ⟨1, by decide⟩
      (UInt256.ofNat input.size) hd (by
        simp [p262, padSized, padBodyStart, padEntry, pushedPad, pushedOutput,
          pushedReturn, hinitStack]) (by
        simp [p262, padSized, padBodyStart, padEntry, pushedPad, pushedOutput,
          pushedReturn, hinitStack]) (by rfl) (by rfl)
    simpa [p263] using g
  have g263 : Challenge.EvmProof.GasSteps (p263 input) (p264 input) := by
    have hd := Trace.decodedOpAt (p263 input) 263 .ADD rfl h263 rfl
      (by decide) trivial (by rfl)
    have g := Challenge.EvmProof.GasStep.add (s := p263 input)
      (a := UInt256.ofNat input.size) (b := UInt256.ofNat 72)
      (rest := [UInt256.ofNat input.size, ⟨0⟩, UInt256.ofNat 1367]) hd (by
      simp [p263, p262, padSized, padBodyStart, padEntry, pushedPad,
        pushedOutput, pushedReturn, hinitStack]) (by
      simp [p263, p262, padSized, padBodyStart, padEntry, pushedPad,
        pushedOutput, pushedReturn, hinitStack, Operation.pushArity,
        Operation.popArity]) (by rfl) (by rfl)
    simpa [p264, p263, p262, padSized, hinitStack, hbodyStack] using g
  have g264 : Challenge.EvmProof.GasSteps (p264 input) (p265 input) := by
    have hd := Trace.decodedPushAt (p264 input) 264 ⟨1, by decide⟩
      (UInt256.ofNat 6) rfl h264 rfl (by decide) (by rfl)
    have g := Challenge.EvmProof.GasStep.pushN (s := p264 input)
      ⟨1, by decide⟩ (UInt256.ofNat 6) 1 (by decide) hd
      (by simp [p264, p263, p262, padSized, padBodyStart, padEntry, pushedPad,
        pushedOutput, pushedReturn, hinitStack]) (by rfl) (by rfl)
    simpa [p265] using g
  have g265 : Challenge.EvmProof.GasSteps (p265 input) (p266 input) := by
    have hd := Trace.decodedOpAt (p265 input) 265 .SHR rfl h265 rfl
      (by decide) trivial (by rfl)
    have g := Challenge.EvmProof.GasStep.shr (s := p265 input)
      (shift := UInt256.ofNat 6)
      (value := UInt256.ofNat input.size + UInt256.ofNat 72)
      (rest := [UInt256.ofNat input.size, ⟨0⟩, UInt256.ofNat 1367]) hd (by
      simp [p265, p264, p263, p262, padSized, padBodyStart, padEntry,
        pushedPad, pushedOutput, pushedReturn, hinitStack]) (by
      simp [p265, p264, p263, p262, padSized, padBodyStart, padEntry,
        pushedPad, pushedOutput, pushedReturn, hinitStack,
        Operation.pushArity, Operation.popArity]) (by rfl) (by rfl)
    simpa [p266, p265, p264, p263, p262, padSized, hinitStack,
      hbodyStack] using g
  have g266 : Challenge.EvmProof.GasSteps (p266 input) (p267 input) := by
    have hd := Trace.decodedPushAt (p266 input) 266 ⟨1, by decide⟩
      (UInt256.ofNat 6) rfl h266 rfl (by decide) (by rfl)
    have g := Challenge.EvmProof.GasStep.pushN (s := p266 input)
      ⟨1, by decide⟩ (UInt256.ofNat 6) 1 (by decide) hd
      (by simp [p266, p265, p264, p263, p262, padSized, padBodyStart,
        padEntry, pushedPad, pushedOutput, pushedReturn, hinitStack])
      (by rfl) (by rfl)
    simpa [p267] using g
  have g267 : Challenge.EvmProof.GasSteps (p267 input) (p268 input) := by
    have hd := Trace.decodedOpAt (p267 input) 267 .SHL rfl h267 rfl
      (by decide) trivial (by rfl)
    have g := Challenge.EvmProof.GasStep.shl (s := p267 input)
      (shift := UInt256.ofNat 6)
      (value := UInt256.shiftRight
        (UInt256.ofNat input.size + UInt256.ofNat 72) (UInt256.ofNat 6))
      (rest := [UInt256.ofNat input.size, ⟨0⟩, UInt256.ofNat 1367]) hd (by
      simp [p267, p266, p265, p264, p263, p262, padSized, padBodyStart,
        padEntry, pushedPad, pushedOutput, pushedReturn, hinitStack]) (by
      simp [p267, p266, p265, p264, p263, p262, padSized, padBodyStart,
        padEntry, pushedPad, pushedOutput, pushedReturn, hinitStack,
        Operation.pushArity, Operation.popArity]) (by rfl) (by rfl)
    simpa [p268, Padding.paddedWord, p267, p266, p265, p264, p263, p262,
      padSized, hinitStack, hbodyStack] using g
  have g268 : Challenge.EvmProof.GasSteps (p268 input) (p269 input) := by
    have hd := Trace.decodedOpAt (p268 input) 268 (.Swap ⟨1, by decide⟩)
      rfl h268 rfl (by decide) trivial (by rfl)
    have g := Challenge.EvmProof.GasStep.swap (s := p268 input) ⟨1, by decide⟩
      [⟨0⟩, UInt256.ofNat input.size, Padding.paddedWord input,
        UInt256.ofNat 1367] hd (by
          simp [p268, p267, p266, p265, p264, p263, p262, padSized,
            padBodyStart, padEntry, pushedPad, pushedOutput, pushedReturn,
            hinitStack, List.exchange]) (by
          simp [p268, p267, p266, p265, p264, p263, p262, padSized,
            padBodyStart, padEntry, pushedPad, pushedOutput, pushedReturn,
            hinitStack, Operation.pushArity, Operation.popArity])
      (by rfl) (by rfl)
    simpa [p269] using g
  have g269 : Challenge.EvmProof.GasSteps (p269 input) (padLengthReady input) := by
    have hd := Trace.decodedOpAt (p269 input) 269 .POP rfl h269 rfl
      (by decide) trivial (by rfl)
    have g := Challenge.EvmProof.GasStep.pop (s := p269 input) hd (by rfl)
      (by simp [p269, Operation.pushArity, Operation.popArity])
      (by rfl) (by rfl)
    simpa [padLengthReady] using g
  exact g261.trans (g262.trans (g263.trans (g264.trans (g265.trans
    (g266.trans (g267.trans (g268.trans g269)))))))

set_option maxHeartbeats 2000000 in
theorem run_computePaddedLength (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock computePaddedLengthPath
      (padSized input) = some (padLengthReady input) := by
  have h261 : Challenge.EvmProof.Stepper.runLocated computePaddedLength261
      (padSized input) = some (p262 input) := by
    simp [Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, computePaddedLength261,
      p262]
  have h262 : Challenge.EvmProof.Stepper.runLocated computePaddedLength262
      (p262 input) = some (p263 input) := by
    simp [Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, computePaddedLength262,
      p263]
  have h263 : Challenge.EvmProof.Stepper.runLocated computePaddedLength263
      (p263 input) = some (p264 input) := by
    simp [Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, computePaddedLength263,
      p264]
  have h264 : Challenge.EvmProof.Stepper.runLocated computePaddedLength264
      (p264 input) = some (p265 input) := by
    simp [Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, computePaddedLength264,
      p265]
  have h265 : Challenge.EvmProof.Stepper.runLocated computePaddedLength265
      (p265 input) = some (p266 input) := by
    simp [Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, computePaddedLength265,
      p266]
  have h266 : Challenge.EvmProof.Stepper.runLocated computePaddedLength266
      (p266 input) = some (p267 input) := by
    simp [Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, computePaddedLength266,
      p267]
  have h267 : Challenge.EvmProof.Stepper.runLocated computePaddedLength267
      (p267 input) = some (p268 input) := by
    simp [Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, computePaddedLength267,
      p268, Padding.paddedWord]
  have h268 : Challenge.EvmProof.Stepper.runLocated computePaddedLength268
      (p268 input) = some (p269 input) := by
    simp [Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, computePaddedLength268,
      p269, List.exchange]
  have h269 : Challenge.EvmProof.Stepper.runLocated computePaddedLength269
      (p269 input) = some (padLengthReady input) := by
    simp [Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, computePaddedLength269,
      padLengthReady]
  simp only [computePaddedLengthPath,
    Challenge.EvmProof.Stepper.runLocatedBlock, h261, h262, h263, h264,
    h265, h266, h267, h268, h269]
  rfl

def gasSteps_computePaddedLength (input : ByteArray) :
    Challenge.EvmProof.GasSteps (padSized input) (padLengthReady input) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka computePaddedLengthPath
  · rfl
  · rfl
  · exact run_computePaddedLength input
  · rfl
  · rfl

@[simp] theorem gasSteps_computePaddedLength_cost (input : ByteArray) :
    (gasSteps_computePaddedLength input).cost = 26 := by
  change Challenge.EvmProof.Stepper.runLocatedBlockCost
    computePaddedLengthPath (padSized input) = 26
  have hstatic : ∀ located, located ∈ computePaddedLengthPath → ∀ q,
      q.fork = .Osaka →
        Challenge.EvmProof.Meter.instrCostWithoutMemory located.instruction q =
          Challenge.EvmProof.Meter.instrStaticCost .Osaka
            located.instruction := by
    intro located hlocated q _
    simp only [computePaddedLengthPath, List.mem_cons, List.not_mem_nil,
      or_false] at hlocated
    rcases hlocated with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [computePaddedLength261, computePaddedLength262,
        computePaddedLength263, computePaddedLength264,
        computePaddedLength265, computePaddedLength266,
        computePaddedLength267, computePaddedLength268,
        computePaddedLength269,
        Challenge.EvmProof.Meter.instrCostWithoutMemory,
        Challenge.EvmProof.Meter.instrStaticCost, Gas.baseCost]
  have hcost := Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    computePaddedLengthPath (run_computePaddedLength input) (by rfl) hstatic
  have hwords : (padLengthReady input).activeWords =
      (padSized input).activeWords := by rfl
  rw [hwords] at hcost
  norm_num [Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
    computePaddedLengthPath, computePaddedLength261, computePaddedLength262,
    computePaddedLength263, computePaddedLength264, computePaddedLength265,
    computePaddedLength266, computePaddedLength267, computePaddedLength268,
    computePaddedLength269, Challenge.EvmProof.Meter.instrStaticCost,
    Gas.baseCost] at hcost ⊢
  omega

set_option maxHeartbeats 2000000 in
private theorem run_lengthSetup (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      lengthSetupPath (padLengthReady input) = some (lengthLoopState input 0) := by
  have hsize : input.size < 2 ^ 256 := by
    exact Nat.lt_trans hfit (by norm_num)
  have hoff : Padding.messageOffset < 2 ^ 256 := by decide
  have hsum : Padding.messageOffset + input.size < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num [Padding.messageOffset] at hfit ⊢
    omega
  have hadd : (UInt256.ofNat Padding.messageOffset +
      UInt256.ofNat input.size).toNat = Padding.messageOffset + input.size := by
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat hsum,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsum]
  have hsizeWord : (UInt256.ofNat input.size).toNat = input.size := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize]
  have hoffWord : (UInt256.ofNat Padding.messageOffset).toNat =
      Padding.messageOffset := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  simp [lengthSetupPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthLoopState, lengthLoopMemory, lengthLoopActiveWords, lengthLoopStart,
    padSentinel, padCopied, lengthOffsetWord, bitLengthWord,
    State.activeWordsAfterUInt256, hsizeWord, hoffWord, hzero, hadd]

def gasSteps_lengthSetup (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (padLengthReady input) (lengthLoopState input 0) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.referenceArtifact
    .Osaka lengthSetupPath
  · rfl
  · exact padLengthReady_fork input
  · exact run_lengthSetup input hfit
  · rfl
  · rfl

@[simp] private theorem lengthLoopStart_halt (input : ByteArray) :
    (lengthLoopStart input).halt = .Running := by rfl

@[simp] private theorem lengthLoopStart_code (input : ByteArray) :
    (lengthLoopStart input).executionEnv.code = referenceBytecode := by rfl

@[simp] private theorem lengthLoopState_halt (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).halt = .Running := by rfl

@[simp] private theorem lengthLoopState_fork (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).fork = .Osaka := by
  exact padLengthReady_fork input

@[simp] private theorem lengthLoopState_code (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).executionEnv.code = referenceBytecode := by rfl

@[simp] private theorem lengthLoopState_pc (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).pc = UInt256.ofNat 399 := by
  simp [lengthLoopState, lengthLoopStart]

@[simp] private theorem lengthLoopState_stack (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).stack =
      [UInt256.ofNat i, lengthOffsetWord input, bitLengthWord input,
        UInt256.ofNat input.size, Padding.paddedWord input, UInt256.ofNat 1367] := by
  rfl

def lengthConditionPath := lengthIterationPath.take 6
def lengthBytePath := (lengthIterationPath.drop 6).take 9
def lengthStorePath := (lengthIterationPath.drop 15).take 4
def lengthIncrementPath := (lengthIterationPath.drop 19).take 5
def lengthBackPath := lengthIterationPath.drop 24

def lengthBodyState (input : ByteArray) (i : Nat) : State :=
  { lengthLoopState input i with pc := UInt256.ofNat 408 }

def lengthByteState (input : ByteArray) (i : Nat) : State :=
  { lengthLoopState input i with
    pc := UInt256.ofNat 420
    stack := [lengthByteWord input i, UInt256.ofNat i,
      lengthOffsetWord input, bitLengthWord input, UInt256.ofNat input.size,
      Padding.paddedWord input, UInt256.ofNat 1367] }

def lengthStoredState (input : ByteArray) (i : Nat) : State :=
  { lengthLoopState input i with
    pc := UInt256.ofNat 424
    memory := lengthLoopMemory input (i + 1)
    activeWords := lengthLoopActiveWords input (i + 1) }

def lengthIncrementedState (input : ByteArray) (i : Nat) : State :=
  { lengthStoredState input i with
    pc := UInt256.ofNat 430
    stack := [UInt256.ofNat (i + 1), lengthOffsetWord input,
      bitLengthWord input, UInt256.ofNat input.size,
      Padding.paddedWord input, UInt256.ofNat 1367] }

set_option maxHeartbeats 200000 in
private theorem run_lengthCondition (input : ByteArray) (i : Nat) (hi : i < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthConditionPath
      (lengthLoopState input i) = some (lengthBodyState input i) := by
  have hi256 : i < 2 ^ 256 := by omega
  have hiWord : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hi256]
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat 8) = UInt256.ofNat 1 := by
    simp [UInt256.lt, hiWord, Challenge.EvmProof.Word.word_toNat_ofNat, hi]
  have hzero : UInt256.isZero (UInt256.ofNat 1) = (⟨0⟩ : UInt256) := by decide
  have hzeroToNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
  simp [lengthConditionPath, lengthIterationPath,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, lengthLoopState, lengthBodyState,
    UInt256.isTrue, hlt, hzero, hzeroToNat, lengthLoopStart_halt]

set_option maxHeartbeats 200000 in
private theorem run_lengthByte (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthBytePath
      (lengthBodyState input i) = some (lengthByteState input i) := by
  simp [lengthBytePath, lengthIterationPath,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, lengthBodyState, lengthByteState,
    lengthLoopState, lengthByteWord]

set_option maxHeartbeats 200000 in
private theorem run_lengthStore (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthStorePath
      (lengthByteState input i) = some (lengthStoredState input i) := by
  simp [lengthStorePath, lengthIterationPath,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, lengthByteState, lengthStoredState,
    lengthLoopState, lengthLoopMemory, lengthLoopActiveWords,
    State.activeWordsAfterUInt256]

set_option maxHeartbeats 200000 in
private theorem run_lengthIncrement (input : ByteArray) (i : Nat) (hi : i < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthIncrementPath
      (lengthStoredState input i) = some (lengthIncrementedState input i) := by
  have hiSucc : i + 1 < 2 ^ 256 := by omega
  have hadd : UInt256.ofNat i + UInt256.ofNat 1 = UInt256.ofNat (i + 1) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat hiSucc
  simp [lengthIncrementPath, lengthIterationPath,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, lengthStoredState, lengthIncrementedState,
    lengthLoopState, hadd, List.exchange]

set_option maxHeartbeats 200000 in
private theorem run_lengthBack (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthBackPath
      (lengthIncrementedState input i) = some (lengthLoopState input (i + 1)) := by
  simp [lengthBackPath, lengthIterationPath,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, lengthIncrementedState, lengthStoredState,
    lengthLoopState, lengthLoopStart_code]

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
  have g₅ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthBackPath (by rfl) (by rfl)
    (run_lengthBack input i) (by rfl) (by rfl)
  exact g₁.trans (g₂.trans (g₃.trans (g₄.trans g₅)))

def gasSteps_lengthLoop (input : ByteArray) :
    Challenge.EvmProof.GasSteps (lengthLoopState input 0)
      (lengthLoopState input 8) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded (count := 8)
    (I := lengthLoopState input)
    (fun i hi => gasSteps_lengthIteration input i hi)

/-- State returned by `pad`: the padded byte length is its sole result. -/
def padReturned (input : ByteArray) : State :=
  { lengthLoopState input 8 with
    pc := UInt256.ofNat 1367
    stack := [Padding.paddedWord input] }

@[simp] theorem padReturned_pc (input : ByteArray) :
    (padReturned input).pc = UInt256.ofNat 1367 := by rfl

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

def lengthExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨289, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨290, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨291, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨292, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨293, .push ⟨2, by decide⟩ (UInt256.ofNat 434), by rfl, by decide⟩,
   ⟨294, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨315, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨316, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨317, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨318, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨319, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨320, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨321, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem refPc316 : Artifact.referenceArtifact.instructionPC 316 = 435 := by decide
@[simp] private theorem refPc317 : Artifact.referenceArtifact.instructionPC 317 = 436 := by decide
@[simp] private theorem refPc318 : Artifact.referenceArtifact.instructionPC 318 = 437 := by decide
@[simp] private theorem refPc319 : Artifact.referenceArtifact.instructionPC 319 = 438 := by decide
@[simp] private theorem refPc320 : Artifact.referenceArtifact.instructionPC 320 = 439 := by decide
@[simp] private theorem refPc321 : Artifact.referenceArtifact.instructionPC 321 = 440 := by decide
@[simp] private theorem refPc711 : Artifact.referenceArtifact.instructionPC 711 = 1367 := by decide
@[simp] private theorem next315 : (UInt256.ofNat 434).succ = UInt256.ofNat 435 := by decide
@[simp] private theorem next316 : (UInt256.ofNat 435).succ = UInt256.ofNat 436 := by decide
@[simp] private theorem next317 : (UInt256.ofNat 436).succ = UInt256.ofNat 437 := by decide
@[simp] private theorem next318 : (UInt256.ofNat 437).succ = UInt256.ofNat 438 := by decide
@[simp] private theorem next319 : (UInt256.ofNat 438).succ = UInt256.ofNat 439 := by decide
@[simp] private theorem next320 : (UInt256.ofNat 439).succ = UInt256.ofNat 440 := by decide

@[simp] private theorem valid434 :
    Decode.isValidJumpDest referenceBytecode 434 = true := by
  rw [← refPc315]
  exact Artifact.isValidJumpDest_index 315 (by rfl)

@[simp] private theorem valid1367 :
    Decode.isValidJumpDest referenceBytecode 1367 = true := by
  rw [← refPc711]
  exact Artifact.isValidJumpDest_index 711 (by rfl)

def lengthExitComparePath := lengthExitPath.take 3
def lengthExitBranchPath := (lengthExitPath.drop 3).take 3
def lengthExitPopPath := (lengthExitPath.drop 6).take 5
def lengthExitReturnPath := lengthExitPath.drop 11

def lengthExitComparedState (input : ByteArray) : State :=
  { lengthLoopState input 8 with
    pc := UInt256.ofNat 403
    stack := [⟨0⟩, UInt256.ofNat 8, lengthOffsetWord input,
      bitLengthWord input, UInt256.ofNat input.size,
      Padding.paddedWord input, UInt256.ofNat 1367] }

def lengthExitBodyState (input : ByteArray) : State :=
  { lengthLoopState input 8 with pc := UInt256.ofNat 434 }

def lengthExitPoppedState (input : ByteArray) : State :=
  { lengthLoopState input 8 with
    pc := UInt256.ofNat 439
    stack := [Padding.paddedWord input, UInt256.ofNat 1367] }

set_option maxHeartbeats 200000 in
private theorem run_lengthExitCompare (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthExitComparePath
      (lengthLoopState input 8) = some (lengthExitComparedState input) := by
  have hlt : UInt256.lt (UInt256.ofNat 8) (UInt256.ofNat 8) = (⟨0⟩ : UInt256) := by
    decide
  simp [lengthExitComparePath, lengthExitPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthExitComparedState, hlt]

set_option maxHeartbeats 200000 in
private theorem run_lengthExitBranch (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthExitBranchPath
      (lengthExitComparedState input) = some (lengthExitBodyState input) := by
  have hzero : UInt256.isZero (⟨0⟩ : UInt256) = UInt256.ofNat 1 := by decide
  simp [lengthExitBranchPath, lengthExitPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthExitComparedState, lengthExitBodyState, UInt256.isTrue, hzero]

set_option maxHeartbeats 200000 in
private theorem run_lengthExitPop (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthExitPopPath
      (lengthExitBodyState input) = some (lengthExitPoppedState input) := by
  simp [lengthExitPopPath, lengthExitPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthExitBodyState, lengthExitPoppedState]

set_option maxHeartbeats 200000 in
private theorem run_lengthExitReturn (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthExitReturnPath
      (lengthExitPoppedState input) = some (padReturned input) := by
  simp [lengthExitReturnPath, lengthExitPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthExitPoppedState, padReturned, List.exchange]

def gasSteps_lengthExit (input : ByteArray) :
    Challenge.EvmProof.GasSteps (lengthLoopState input 8) (padReturned input) := by
  have g₁ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthExitComparePath
    (lengthLoopState_code input 8) (lengthLoopState_fork input 8)
    (run_lengthExitCompare input) (lengthLoopState_halt input 8) (by rfl)
  have g₂ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthExitBranchPath (by rfl) (by rfl)
    (run_lengthExitBranch input) (by rfl) (by rfl)
  have g₃ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthExitPopPath (by rfl) (by rfl)
    (run_lengthExitPop input) (by rfl) (by rfl)
  have g₄ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthExitReturnPath (by rfl) (by rfl)
    (run_lengthExitReturn input) (by rfl) (by rfl)
  exact g₁.trans (g₂.trans (g₃.trans g₄))

theorem bitLengthWord_eq (input : ByteArray) (hfit : CalldataFits input) :
    bitLengthWord input = UInt256.ofNat (input.size * 8) := by
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hresult : input.size * 2 ^ 3 < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num at hfit ⊢
    omega
  simpa [bitLengthWord] using
    (Challenge.EvmProof.Word.shiftLeft_ofNat hsize (by decide : 3 < 256) hresult)

private theorem seven_sub_word (i : Nat) (hi : i < 8) :
    UInt256.ofNat 7 - UInt256.ofNat i = UInt256.ofNat (7 - i) := by
  have hi256 : i < 2 ^ 256 := by omega
  have hiWord : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hi256]
  have h7Word : (UInt256.ofNat 7).toNat = 7 := by decide
  have hsmall : 7 - i < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.sub_le 7 i) (by norm_num)
  have hsubWord : (UInt256.ofNat (7 - i)).toNat = 7 - i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsmall]
  apply Challenge.EvmProof.Word.word_ext
  change ((UInt256.ofNat 7).val - (UInt256.ofNat i).val).val = _
  rw [Fin.val_sub]
  change (UInt256.size - (UInt256.ofNat i).toNat +
    (UInt256.ofNat 7).toNat) % UInt256.size =
      (UInt256.ofNat (7 - i)).toNat
  rw [hiWord, h7Word, hsubWord]
  have hrearrange : UInt256.size - i + 7 = UInt256.size + (7 - i) := by
    change 2 ^ 256 - i + 7 = 2 ^ 256 + (7 - i)
    omega
  rw [hrearrange, Nat.add_mod]
  rw [Nat.mod_self, Nat.zero_add]
  change ((7 - i) % 2 ^ 256) % 2 ^ 256 = 7 - i
  rw [Nat.mod_eq_of_lt hsmall, Nat.mod_eq_of_lt hsmall]

theorem lengthByteWord_toNat (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 8) :
    (lengthByteWord input i).toNat =
      input.size * 8 / 256 ^ (7 - i) % 256 := by
  have hvalue : input.size * 8 < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num at hfit ⊢
    omega
  have hshift : (7 - i) * 8 < 256 := by omega
  have hshiftValue : 7 - i < 2 ^ 256 := by omega
  have hshiftResult : (7 - i) * 2 ^ 3 < 2 ^ 256 := by omega
  have hshiftWord : UInt256.shiftLeft (UInt256.ofNat (7 - i))
      (UInt256.ofNat 3) = UInt256.ofNat ((7 - i) * 8) := by
    simpa using Challenge.EvmProof.Word.shiftLeft_ofNat hshiftValue
      (by decide : 3 < 256) hshiftResult
  rw [lengthByteWord, bitLengthWord_eq input hfit, seven_sub_word i hi,
    hshiftWord, Challenge.EvmProof.Word.shiftRight_ofNat hvalue hshift]
  simp only [UInt256.land, UInt256.toNat]
  have hland : (↑(Fin.land
      (UInt256.ofNat ((input.size * 8) >>> ((7 - i) * 8))).val
      (UInt256.ofNat 255).val) : Nat) =
      (UInt256.ofNat ((input.size * 8) >>> ((7 - i) * 8))).val.val &&&
        (UInt256.ofNat 255).val.val := by
    exact Fin.and_val _ _
  rw [hland]
  change (UInt256.ofNat ((input.size * 8) >>> ((7 - i) * 8))).toNat &&&
      (UInt256.ofNat 255).toNat = _
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hvalue)]
  have h255 : (UInt256.ofNat 255).toNat = 255 := by decide
  rw [h255, show 255 = 2 ^ 8 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  rw [show 2 ^ ((7 - i) * 8) = 256 ^ (7 - i) by
    rw [Nat.mul_comm, Nat.pow_mul]]

theorem lengthByte_eq (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 8) :
    UInt8.ofNat ((lengthByteWord input i).toNat % 256) =
      (Padding.lengthBytes input)[i]?.getD 0 := by
  change UInt8.ofNat ((lengthByteWord input i).toNat % 256) =
    (Data.Bytes.natToBytesPadded (input.size * 8) 8)[i]?.getD 0
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD
    (input.size * 8) 8 i hi]
  rw [show 8 - 1 - i = 7 - i by omega]
  rw [lengthByteWord_toNat input hfit i hi]
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
    have hoffset : Padding.messageOffset + Padding.paddedLength input.size <
        2 ^ 256 := by
      calc
        Padding.messageOffset + Padding.paddedLength input.size <
            Padding.messageOffset + (input.size + 73) :=
          Nat.add_lt_add_left hlt _
        _ < 2 ^ 256 := by
          have hinput73 : input.size + 73 < 2 ^ 65 := by
            unfold CalldataFits at hfit
            norm_num at hfit ⊢
            omega
          calc
            Padding.messageOffset + (input.size + 73) <
                Padding.messageOffset + 2 ^ 65 :=
              Nat.add_lt_add_left hinput73 _
            _ < 2 ^ 256 := by norm_num [Padding.messageOffset]
    exact Nat.lt_of_le_of_lt
      (Nat.add_le_add_left (Nat.sub_le (Padding.paddedLength input.size) 8) _)
      hoffset
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
  | succ i ih =>
      rw [lengthWrittenBytes, ByteArray.size_append, ih]
      rfl

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
        rw [if_neg (by omega)]
        rw [Nat.sub_self]
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

/-- Complete certified execution of initialization and the reference `pad`
function, exposing the canonical padded-memory model. -/
def gasSteps_pad (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (padReturned input) :=
  (Main.gasSteps_initialize input).trans
    ((gasSteps_enterPad input).trans
      ((gasSteps_padReadSize input).trans
        ((gasSteps_computePaddedLength input).trans
          ((gasSteps_lengthSetup input hfit).trans
            ((gasSteps_lengthLoop input).trans (gasSteps_lengthExit input))))))

theorem padReturned_memory (input : ByteArray) (hfit : CalldataFits input) :
    (padReturned input).memory =
      Padding.paddedMemory (padLengthReady input).memory input := by
  exact lengthLoopMemory_eight input hfit

end Challenge.Sha256.Reference.Proofs.Bytecode.PaddingTrace
