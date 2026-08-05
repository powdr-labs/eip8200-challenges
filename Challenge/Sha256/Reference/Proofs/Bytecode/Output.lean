import Challenge.Sha256.Reference.Proofs.Bytecode.Accessors
import Challenge.EvmProof.Memory
set_option warningAsError true
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
/-!
# Certified digest output for the reference SHA bytecode

The final bytecode block loads the eight chaining-state words through the
internal `hAt` helper, packs them into one big-endian 256-bit word, stores that
word at memory offset zero, and returns the resulting 32 bytes.  The summaries
in this file deliberately start from an arbitrary running state: callers only
need to establish the code/fork facts and the output-block entry stack.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.Output

open EvmSemantics
open EvmSemantics.EVM

@[simp] private theorem succSmall (n : Nat) (h : n + 1 < 2 ^ 256) :
    (UInt256.ofNat n).succ = UInt256.ofNat (n + 1) :=
  Challenge.EvmProof.Word.succ_ofNat h

@[simp] private theorem addSmall (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.EvmProof.Word.ofNat_add_ofNat h

private theorem uintZero : (0 : UInt256) = UInt256.ofNat 0 := by decide

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

/-! The optimized artifact inlines the output block into the driver loop's exit
and reads the eight chaining words with plain `MLOAD`s at fixed offsets instead
of calling the `hAt` accessor eight times.  That collapses the old
`startPath` + seven `setupNPath` + `finishPath` decomposition — and the eight
call/return proofs that went with it — into one straight run of 44 instructions,
instructions 86 through 129.

The packing expression is unchanged: the backend emits the same `OR` tree in the
same association, so `pair67`, `pair45`, `lowHalf`, `pair23` and `digestWord`
below are exactly as they were. -/

@[simp] private theorem pc86 :
    Artifact.referenceArtifact.instructionPC 86 = 415 := by decide

@[simp] private theorem pc87 :
    Artifact.referenceArtifact.instructionPC 87 = 416 := by decide

@[simp] private theorem pc88 :
    Artifact.referenceArtifact.instructionPC 88 = 417 := by decide

@[simp] private theorem pc89 :
    Artifact.referenceArtifact.instructionPC 89 = 420 := by decide

@[simp] private theorem pc90 :
    Artifact.referenceArtifact.instructionPC 90 = 421 := by decide

@[simp] private theorem pc91 :
    Artifact.referenceArtifact.instructionPC 91 = 424 := by decide

@[simp] private theorem pc92 :
    Artifact.referenceArtifact.instructionPC 92 = 425 := by decide

@[simp] private theorem pc93 :
    Artifact.referenceArtifact.instructionPC 93 = 427 := by decide

@[simp] private theorem pc94 :
    Artifact.referenceArtifact.instructionPC 94 = 428 := by decide

@[simp] private theorem pc95 :
    Artifact.referenceArtifact.instructionPC 95 = 429 := by decide

@[simp] private theorem pc96 :
    Artifact.referenceArtifact.instructionPC 96 = 432 := by decide

@[simp] private theorem pc97 :
    Artifact.referenceArtifact.instructionPC 97 = 433 := by decide

@[simp] private theorem pc98 :
    Artifact.referenceArtifact.instructionPC 98 = 435 := by decide

@[simp] private theorem pc99 :
    Artifact.referenceArtifact.instructionPC 99 = 436 := by decide

@[simp] private theorem pc100 :
    Artifact.referenceArtifact.instructionPC 100 = 439 := by decide

@[simp] private theorem pc101 :
    Artifact.referenceArtifact.instructionPC 101 = 440 := by decide

@[simp] private theorem pc102 :
    Artifact.referenceArtifact.instructionPC 102 = 442 := by decide

@[simp] private theorem pc103 :
    Artifact.referenceArtifact.instructionPC 103 = 443 := by decide

@[simp] private theorem pc104 :
    Artifact.referenceArtifact.instructionPC 104 = 444 := by decide

@[simp] private theorem pc105 :
    Artifact.referenceArtifact.instructionPC 105 = 445 := by decide

@[simp] private theorem pc106 :
    Artifact.referenceArtifact.instructionPC 106 = 448 := by decide

@[simp] private theorem pc107 :
    Artifact.referenceArtifact.instructionPC 107 = 449 := by decide

@[simp] private theorem pc108 :
    Artifact.referenceArtifact.instructionPC 108 = 451 := by decide

@[simp] private theorem pc109 :
    Artifact.referenceArtifact.instructionPC 109 = 452 := by decide

@[simp] private theorem pc110 :
    Artifact.referenceArtifact.instructionPC 110 = 455 := by decide

@[simp] private theorem pc111 :
    Artifact.referenceArtifact.instructionPC 111 = 456 := by decide

@[simp] private theorem pc112 :
    Artifact.referenceArtifact.instructionPC 112 = 458 := by decide

@[simp] private theorem pc113 :
    Artifact.referenceArtifact.instructionPC 113 = 459 := by decide

@[simp] private theorem pc114 :
    Artifact.referenceArtifact.instructionPC 114 = 460 := by decide

@[simp] private theorem pc115 :
    Artifact.referenceArtifact.instructionPC 115 = 463 := by decide

@[simp] private theorem pc116 :
    Artifact.referenceArtifact.instructionPC 116 = 464 := by decide

@[simp] private theorem pc117 :
    Artifact.referenceArtifact.instructionPC 117 = 466 := by decide

@[simp] private theorem pc118 :
    Artifact.referenceArtifact.instructionPC 118 = 467 := by decide

@[simp] private theorem pc119 :
    Artifact.referenceArtifact.instructionPC 119 = 470 := by decide

@[simp] private theorem pc120 :
    Artifact.referenceArtifact.instructionPC 120 = 471 := by decide

@[simp] private theorem pc121 :
    Artifact.referenceArtifact.instructionPC 121 = 473 := by decide

@[simp] private theorem pc122 :
    Artifact.referenceArtifact.instructionPC 122 = 474 := by decide

@[simp] private theorem pc123 :
    Artifact.referenceArtifact.instructionPC 123 = 475 := by decide

@[simp] private theorem pc124 :
    Artifact.referenceArtifact.instructionPC 124 = 476 := by decide

@[simp] private theorem pc125 :
    Artifact.referenceArtifact.instructionPC 125 = 477 := by decide

@[simp] private theorem pc126 :
    Artifact.referenceArtifact.instructionPC 126 = 478 := by decide

@[simp] private theorem pc127 :
    Artifact.referenceArtifact.instructionPC 127 = 479 := by decide

@[simp] private theorem pc128 :
    Artifact.referenceArtifact.instructionPC 128 = 481 := by decide

@[simp] private theorem pc129 :
    Artifact.referenceArtifact.instructionPC 129 = 482 := by decide

@[simp] private theorem pc130 :
    Artifact.referenceArtifact.instructionPC 130 = 483 := by decide

@[simp] private theorem next86 : (UInt256.ofNat 415).succ = UInt256.ofNat 416 := by decide
@[simp] private theorem next87 : (UInt256.ofNat 416).succ = UInt256.ofNat 417 := by decide
@[simp] private theorem next88 : UInt256.ofNat 417 + UInt256.ofNat 3 = UInt256.ofNat 420 := by decide
@[simp] private theorem next89 : (UInt256.ofNat 420).succ = UInt256.ofNat 421 := by decide
@[simp] private theorem next90 : UInt256.ofNat 421 + UInt256.ofNat 3 = UInt256.ofNat 424 := by decide
@[simp] private theorem next91 : (UInt256.ofNat 424).succ = UInt256.ofNat 425 := by decide
@[simp] private theorem next92 : UInt256.ofNat 425 + UInt256.ofNat 2 = UInt256.ofNat 427 := by decide
@[simp] private theorem next93 : (UInt256.ofNat 427).succ = UInt256.ofNat 428 := by decide
@[simp] private theorem next94 : (UInt256.ofNat 428).succ = UInt256.ofNat 429 := by decide
@[simp] private theorem next95 : UInt256.ofNat 429 + UInt256.ofNat 3 = UInt256.ofNat 432 := by decide
@[simp] private theorem next96 : (UInt256.ofNat 432).succ = UInt256.ofNat 433 := by decide
@[simp] private theorem next97 : UInt256.ofNat 433 + UInt256.ofNat 2 = UInt256.ofNat 435 := by decide
@[simp] private theorem next98 : (UInt256.ofNat 435).succ = UInt256.ofNat 436 := by decide
@[simp] private theorem next99 : UInt256.ofNat 436 + UInt256.ofNat 3 = UInt256.ofNat 439 := by decide
@[simp] private theorem next100 : (UInt256.ofNat 439).succ = UInt256.ofNat 440 := by decide
@[simp] private theorem next101 : UInt256.ofNat 440 + UInt256.ofNat 2 = UInt256.ofNat 442 := by decide
@[simp] private theorem next102 : (UInt256.ofNat 442).succ = UInt256.ofNat 443 := by decide
@[simp] private theorem next103 : (UInt256.ofNat 443).succ = UInt256.ofNat 444 := by decide
@[simp] private theorem next104 : (UInt256.ofNat 444).succ = UInt256.ofNat 445 := by decide
@[simp] private theorem next105 : UInt256.ofNat 445 + UInt256.ofNat 3 = UInt256.ofNat 448 := by decide
@[simp] private theorem next106 : (UInt256.ofNat 448).succ = UInt256.ofNat 449 := by decide
@[simp] private theorem next107 : UInt256.ofNat 449 + UInt256.ofNat 2 = UInt256.ofNat 451 := by decide
@[simp] private theorem next108 : (UInt256.ofNat 451).succ = UInt256.ofNat 452 := by decide
@[simp] private theorem next109 : UInt256.ofNat 452 + UInt256.ofNat 3 = UInt256.ofNat 455 := by decide
@[simp] private theorem next110 : (UInt256.ofNat 455).succ = UInt256.ofNat 456 := by decide
@[simp] private theorem next111 : UInt256.ofNat 456 + UInt256.ofNat 2 = UInt256.ofNat 458 := by decide
@[simp] private theorem next112 : (UInt256.ofNat 458).succ = UInt256.ofNat 459 := by decide
@[simp] private theorem next113 : (UInt256.ofNat 459).succ = UInt256.ofNat 460 := by decide
@[simp] private theorem next114 : UInt256.ofNat 460 + UInt256.ofNat 3 = UInt256.ofNat 463 := by decide
@[simp] private theorem next115 : (UInt256.ofNat 463).succ = UInt256.ofNat 464 := by decide
@[simp] private theorem next116 : UInt256.ofNat 464 + UInt256.ofNat 2 = UInt256.ofNat 466 := by decide
@[simp] private theorem next117 : (UInt256.ofNat 466).succ = UInt256.ofNat 467 := by decide
@[simp] private theorem next118 : UInt256.ofNat 467 + UInt256.ofNat 3 = UInt256.ofNat 470 := by decide
@[simp] private theorem next119 : (UInt256.ofNat 470).succ = UInt256.ofNat 471 := by decide
@[simp] private theorem next120 : UInt256.ofNat 471 + UInt256.ofNat 2 = UInt256.ofNat 473 := by decide
@[simp] private theorem next121 : (UInt256.ofNat 473).succ = UInt256.ofNat 474 := by decide
@[simp] private theorem next122 : (UInt256.ofNat 474).succ = UInt256.ofNat 475 := by decide
@[simp] private theorem next123 : (UInt256.ofNat 475).succ = UInt256.ofNat 476 := by decide
@[simp] private theorem next124 : (UInt256.ofNat 476).succ = UInt256.ofNat 477 := by decide
@[simp] private theorem next125 : (UInt256.ofNat 477).succ = UInt256.ofNat 478 := by decide
@[simp] private theorem next126 : (UInt256.ofNat 478).succ = UInt256.ofNat 479 := by decide
@[simp] private theorem next127 : UInt256.ofNat 479 + UInt256.ofNat 2 = UInt256.ofNat 481 := by decide
@[simp] private theorem next128 : (UInt256.ofNat 481).succ = UInt256.ofNat 482 := by decide
@[simp] private theorem next129 : (UInt256.ofNat 482).succ = UInt256.ofNat 483 := by decide


/-! The stepper compares `pc.toNat` against each instruction's PC, so every
program counter this block passes through needs its `toNat`. -/

@[simp] private theorem pcToNat415 : (UInt256.ofNat 415).toNat = 415 := by decide
@[simp] private theorem pcToNat416 : (UInt256.ofNat 416).toNat = 416 := by decide
@[simp] private theorem pcToNat417 : (UInt256.ofNat 417).toNat = 417 := by decide
@[simp] private theorem pcToNat420 : (UInt256.ofNat 420).toNat = 420 := by decide
@[simp] private theorem pcToNat421 : (UInt256.ofNat 421).toNat = 421 := by decide
@[simp] private theorem pcToNat424 : (UInt256.ofNat 424).toNat = 424 := by decide
@[simp] private theorem pcToNat425 : (UInt256.ofNat 425).toNat = 425 := by decide
@[simp] private theorem pcToNat427 : (UInt256.ofNat 427).toNat = 427 := by decide
@[simp] private theorem pcToNat428 : (UInt256.ofNat 428).toNat = 428 := by decide
@[simp] private theorem pcToNat429 : (UInt256.ofNat 429).toNat = 429 := by decide
@[simp] private theorem pcToNat432 : (UInt256.ofNat 432).toNat = 432 := by decide
@[simp] private theorem pcToNat433 : (UInt256.ofNat 433).toNat = 433 := by decide
@[simp] private theorem pcToNat435 : (UInt256.ofNat 435).toNat = 435 := by decide
@[simp] private theorem pcToNat436 : (UInt256.ofNat 436).toNat = 436 := by decide
@[simp] private theorem pcToNat439 : (UInt256.ofNat 439).toNat = 439 := by decide
@[simp] private theorem pcToNat440 : (UInt256.ofNat 440).toNat = 440 := by decide
@[simp] private theorem pcToNat442 : (UInt256.ofNat 442).toNat = 442 := by decide
@[simp] private theorem pcToNat443 : (UInt256.ofNat 443).toNat = 443 := by decide
@[simp] private theorem pcToNat444 : (UInt256.ofNat 444).toNat = 444 := by decide
@[simp] private theorem pcToNat445 : (UInt256.ofNat 445).toNat = 445 := by decide
@[simp] private theorem pcToNat448 : (UInt256.ofNat 448).toNat = 448 := by decide
@[simp] private theorem pcToNat449 : (UInt256.ofNat 449).toNat = 449 := by decide
@[simp] private theorem pcToNat451 : (UInt256.ofNat 451).toNat = 451 := by decide
@[simp] private theorem pcToNat452 : (UInt256.ofNat 452).toNat = 452 := by decide
@[simp] private theorem pcToNat455 : (UInt256.ofNat 455).toNat = 455 := by decide
@[simp] private theorem pcToNat456 : (UInt256.ofNat 456).toNat = 456 := by decide
@[simp] private theorem pcToNat458 : (UInt256.ofNat 458).toNat = 458 := by decide
@[simp] private theorem pcToNat459 : (UInt256.ofNat 459).toNat = 459 := by decide
@[simp] private theorem pcToNat460 : (UInt256.ofNat 460).toNat = 460 := by decide
@[simp] private theorem pcToNat463 : (UInt256.ofNat 463).toNat = 463 := by decide
@[simp] private theorem pcToNat464 : (UInt256.ofNat 464).toNat = 464 := by decide
@[simp] private theorem pcToNat466 : (UInt256.ofNat 466).toNat = 466 := by decide
@[simp] private theorem pcToNat467 : (UInt256.ofNat 467).toNat = 467 := by decide
@[simp] private theorem pcToNat470 : (UInt256.ofNat 470).toNat = 470 := by decide
@[simp] private theorem pcToNat471 : (UInt256.ofNat 471).toNat = 471 := by decide
@[simp] private theorem pcToNat473 : (UInt256.ofNat 473).toNat = 473 := by decide
@[simp] private theorem pcToNat474 : (UInt256.ofNat 474).toNat = 474 := by decide
@[simp] private theorem pcToNat475 : (UInt256.ofNat 475).toNat = 475 := by decide
@[simp] private theorem pcToNat476 : (UInt256.ofNat 476).toNat = 476 := by decide
@[simp] private theorem pcToNat477 : (UInt256.ofNat 477).toNat = 477 := by decide
@[simp] private theorem pcToNat478 : (UInt256.ofNat 478).toNat = 478 := by decide
@[simp] private theorem pcToNat479 : (UInt256.ofNat 479).toNat = 479 := by decide
@[simp] private theorem pcToNat481 : (UInt256.ofNat 481).toNat = 481 := by decide
@[simp] private theorem pcToNat482 : (UInt256.ofNat 482).toNat = 482 := by decide
@[simp] private theorem pcToNat483 : (UInt256.ofNat 483).toNat = 483 := by decide

/-! The `MLOAD` offsets are literals in the bytecode, so the stepper needs
them at `Nat` before it can read memory. -/

@[simp] private theorem toNat0 : (UInt256.ofNat 0).toNat = 0 := by decide
@[simp] private theorem toNat32 : (UInt256.ofNat 32).toNat = 32 := by decide
@[simp] private theorem toNat288 : (UInt256.ofNat 288).toNat = 288 := by decide
@[simp] private theorem toNat320 : (UInt256.ofNat 320).toNat = 320 := by decide
@[simp] private theorem toNat352 : (UInt256.ofNat 352).toNat = 352 := by decide
@[simp] private theorem toNat384 : (UInt256.ofNat 384).toNat = 384 := by decide
@[simp] private theorem toNat416 : (UInt256.ofNat 416).toNat = 416 := by decide
@[simp] private theorem toNat448 : (UInt256.ofNat 448).toNat = 448 := by decide
@[simp] private theorem toNat480 : (UInt256.ofNat 480).toNat = 480 := by decide
@[simp] private theorem toNat512 : (UInt256.ofNat 512).toNat = 512 := by decide

/-- Offset of chaining word `i`: the H slots run from `0x120` to `0x200`. -/
def hOffset (i : Nat) : Nat := 288 + 32 * i

def hWord (s : State) (i : Nat) : UInt256 :=
  MachineState.readWord s.memory (hOffset i)

def pair67 (s : State) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft (hWord s 6) (UInt256.ofNat 32)) (hWord s 7)

def shifted5 (s : State) : UInt256 :=
  UInt256.shiftLeft (hWord s 5) (UInt256.ofNat 64)

def pair45 (s : State) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft (hWord s 4) (UInt256.ofNat 96)) (shifted5 s)

def lowHalf (s : State) : UInt256 := UInt256.lor (pair45 s) (pair67 s)

def shifted3 (s : State) : UInt256 :=
  UInt256.shiftLeft (hWord s 3) (UInt256.ofNat 128)

def pair23 (s : State) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft (hWord s 2) (UInt256.ofNat 160)) (shifted3 s)

def shifted1 (s : State) : UInt256 :=
  UInt256.shiftLeft (hWord s 1) (UInt256.ofNat 192)

/-- The exact 256-bit packing the block computes. -/
def digestWord (s : State) : UInt256 :=
  UInt256.lor
    (UInt256.lor
      (UInt256.lor
        (UInt256.shiftLeft (hWord s 0) (UInt256.ofNat 224)) (shifted1 s))
      (pair23 s))
    (lowHalf s)

def digestBytes (s : State) : ByteArray :=
  Data.Bytes.natToBytesPadded (digestWord s).toNat 32

/-! Each `MLOAD` updates the active-word count, so the accumulation is threaded
through a state per load, exactly as the old proof did.  The eight offsets
descend from `0x200`, so in practice none of them grows the count past what
initialization already touched — but that is a fact about the offsets, not
something `rfl` can see, so the chain stays structural. -/

def afterLoad (s : State) (i : Nat) : State :=
  { s with activeWords := s.activeWordsAfterUInt256 (hOffset i) 32 }

/-- Active-word state after the eight loads, issued in descending offset
order. -/
def afterLoads (s : State) : State :=
  afterLoad (afterLoad (afterLoad (afterLoad (afterLoad (afterLoad
    (afterLoad (afterLoad s 7) 6) 5) 4) 3) 2) 1) 0

/-- `MSTORE` and `RETURN` each touch `[0, 32)`, so the count is stepped twice
more after the loads. -/
def afterStore (s : State) : State :=
  { afterLoads s with
    activeWords := (afterLoads s).activeWordsAfterUInt256 0 32 }

def outputActiveWords (s : State) : UInt256 :=
  (afterStore s).activeWordsAfterUInt256 0 32

/-- The driver loop falls through to the output block with its counter and the
padded length still on the stack; the block's first two instructions drop them. -/
def outputEntry (s : State) (counter padded : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 86)
    stack := counter :: padded :: rest }

/-- Result of the output block: the digest word written at 0 and returned. -/
def outputResult (s : State) (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 129)
    stack := rest
    memory := MachineState.writeBytes s.memory (digestBytes s) 0
    activeWords := outputActiveWords s
    halt := .Returned
    hReturn := digestBytes s }

/-- The single located path for the whole block. -/
def outputPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨86, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨87, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨88, .push ⟨2, by decide⟩ (UInt256.ofNat 0x200), by rfl, by decide⟩,
   ⟨89, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨90, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1e0), by rfl, by decide⟩,
   ⟨91, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨92, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨93, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨94, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨95, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1c0), by rfl, by decide⟩,
   ⟨96, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨97, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨98, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨99, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1a0), by rfl, by decide⟩,
   ⟨100, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨101, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨102, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨103, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨104, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨105, .push ⟨2, by decide⟩ (UInt256.ofNat 0x180), by rfl, by decide⟩,
   ⟨106, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨107, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨108, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨109, .push ⟨2, by decide⟩ (UInt256.ofNat 0x160), by rfl, by decide⟩,
   ⟨110, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨111, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨112, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨113, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨114, .push ⟨2, by decide⟩ (UInt256.ofNat 0x140), by rfl, by decide⟩,
   ⟨115, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨116, .push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨117, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨118, .push ⟨2, by decide⟩ (UInt256.ofNat 0x120), by rfl, by decide⟩,
   ⟨119, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨120, .push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨121, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨122, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨123, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨124, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨125, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨126, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨127, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨128, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨129, .op .RETURN, by rfl, wfOp (by decide) trivial rfl⟩]

/-- `RETURN` reports the memory window it just wrote.  Stated over a bare
`natToBytesPadded` so it fires after the packing expression has been unfolded. -/
@[simp] private theorem readPadded_writeBytes_natToBytesPadded
    (m : ByteArray) (n : Nat) :
    MachineState.readPadded
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded n 32) 0) 0 32 =
      Data.Bytes.natToBytesPadded n 32 := by
  have hsize : (Data.Bytes.natToBytesPadded n 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  simpa [hsize] using Challenge.EvmProof.Memory.readPadded_writeBytes_same
    m (Data.Bytes.natToBytesPadded n 32) 0

@[simp] theorem outputResult_memory (s : State) (rest : List UInt256) :
    (outputResult s rest).memory =
      MachineState.writeBytes s.memory (digestBytes s) 0 := by rfl

set_option maxHeartbeats 4000000 in
theorem run_output (s : State) (counter padded : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1016)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outputPath
      (outputEntry s counter padded rest) = some (outputResult s rest) := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 1 + 1 < 1024 := by omega
  have hc3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have hc4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp [outputPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    outputEntry, outputResult, outputActiveWords, afterStore, afterLoads,
    afterLoad,
    digestBytes, digestWord,
    hOffset, hWord, pair67, pair45, shifted5, lowHalf, pair23, shifted3,
    shifted1, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hrun]

/-- The output block returns exactly the 32-byte big-endian packing of the eight
words in the H slots. -/
def gasSteps_output (s : State) (counter padded : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1016)
    (hcode : (outputEntry s counter padded rest).executionEnv.code =
      referenceBytecode)
    (hfork : (outputEntry s counter padded rest).fork = .Osaka)
    (hrun : s.halt = .Running)
    (hhalt : (outputEntry s counter padded rest).halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig
      (outputEntry s counter padded rest).executionEnv.precompileConfig
      (outputEntry s counter padded rest).executionEnv.fork
      (outputEntry s counter padded rest).executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (outputEntry s counter padded rest)
      (outputResult s rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka outputPath
  · exact hcode
  · exact hfork
  · exact run_output s counter padded rest hcap hrun
  · exact hhalt
  · exact hnp

theorem outputResult_memoryWindow (s : State) (rest : List UInt256) :
    MachineState.readPadded (outputResult s rest).memory 0 32 = digestBytes s := by
  rw [outputResult_memory]
  have hsize : (digestBytes s).size = 32 := by
    simp [digestBytes, Data.Bytes.natToBytesPadded, ByteArray.size]
  simpa [hsize] using Challenge.EvmProof.Memory.readPadded_writeBytes_same
    s.memory (digestBytes s) 0

/-- Reading the returned memory as an EVM word recovers the packed digest. -/
theorem outputResult_readWord (s : State) (rest : List UInt256) :
    MachineState.readWord (outputResult s rest).memory 0 = digestWord s := by
  rw [outputResult_memory]
  exact Challenge.EvmProof.Memory.readWord_writeWord s.memory 0 (digestWord s)

end Challenge.Sha256.Reference.Proofs.Bytecode.Output
