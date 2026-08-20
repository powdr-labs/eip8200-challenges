import Challenge.Modexp.Reference.Proofs.Algorithm
import Challenge.Modexp.Reference.Proofs.Bytecode.Accessors
import Challenge.Modexp.Reference.Proofs.Bytecode.Dispatch
import Challenge.EvmProof.Bytes
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option maxErrors 1
/-!
# One-word MODEXP path

This module certifies the entry of the `MULMOD` fast path and names its loop
invariants.  Operand widths and offsets are expressed with the same padded
byte decoder as the challenge specification.
-/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.Word

open EvmSemantics
open EvmSemantics.EVM

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

theorem wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.referenceInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.referenceInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def startPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 415 .JUMPDEST, opAt 416 (.Dup ⟨5, by decide⟩),
   opAt 417 .CALLDATALOAD, opAt 418 (.Dup ⟨3, by decide⟩),
   pushAt 419 1 32, opAt 420 .SUB, pushAt 421 1 3,
   opAt 422 .SHL, opAt 423 .SHR, opAt 424 (.Dup ⟨0, by decide⟩),
   pushAt 425 2 538, opAt 426 .JUMPI]

def zeroTailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 427 (.Dup ⟨3, by decide⟩), pushAt 428 2 6144,
   opAt 429 .RETURN]

def zeroModulusPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  startPath ++ zeroTailPath

def startLoadPath := startPath.take 11
def startJumpPath := [opAt 426 .JUMPI]

def baseSetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 430 .JUMPDEST, pushAt 431 0 0, pushAt 432 0 0]

def baseGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 433 .JUMPDEST, opAt 434 (.Dup ⟨3, by decide⟩),
   opAt 435 (.Dup ⟨1, by decide⟩), opAt 436 .LT, opAt 437 .ISZERO,
   pushAt 438 2 582, opAt 439 .JUMPI]

def baseCallPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 440 (.Dup ⟨2, by decide⟩), pushAt 441 2 562, pushAt 442 0 0,
   opAt 443 (.Dup ⟨3, by decide⟩), opAt 444 (.Dup ⟨10, by decide⟩),
   opAt 445 .ADD, pushAt 446 2 4, opAt 447 .JUMP]

def baseTailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 448 .JUMPDEST, opAt 449 (.Dup ⟨4, by decide⟩), pushAt 450 2 256,
   opAt 451 (.Dup ⟨5, by decide⟩), opAt 452 .MULMOD, opAt 453 .ADDMOD,
   opAt 454 (.Swap ⟨1, by decide⟩), opAt 455 .POP, pushAt 456 1 1,
   opAt 457 (.Dup ⟨1, by decide⟩), opAt 458 .ADD,
   opAt 459 (.Swap ⟨0, by decide⟩), opAt 460 .POP,
   pushAt 461 2 541, opAt 462 .JUMP]

def baseFinishTailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 463 .JUMPDEST, opAt 464 .POP, opAt 465 (.Dup ⟨1, by decide⟩),
   pushAt 466 1 1, opAt 467 .MOD, pushAt 468 0 0]

def expGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 469 .JUMPDEST, opAt 470 (.Dup ⟨5, by decide⟩),
   opAt 471 (.Dup ⟨1, by decide⟩), opAt 472 .LT, opAt 473 .ISZERO,
   pushAt 474 2 669, opAt 475 .JUMPI]

def expLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 476 (.Dup ⟨0, by decide⟩), opAt 477 (.Dup ⟨9, by decide⟩),
   opAt 478 .ADD, opAt 479 (.Dup ⟨0, by decide⟩), opAt 480 .CALLDATALOAD,
   pushAt 481 0 0, opAt 482 .BYTE, pushAt 483 0 0]

def bitGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 484 .JUMPDEST, pushAt 485 1 8, opAt 486 (.Dup ⟨1, by decide⟩),
   opAt 487 .LT, opAt 488 .ISZERO, pushAt 489 2 655, opAt 490 .JUMPI]

def bitDecodePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [pushAt 491 1 1, opAt 492 (.Dup ⟨2, by decide⟩),
   opAt 493 (.Dup ⟨2, by decide⟩), pushAt 494 1 7, opAt 495 .SUB,
   opAt 496 .SHR, opAt 497 .AND]

def bitSquarePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 498 (.Dup ⟨7, by decide⟩), opAt 499 (.Dup ⟨6, by decide⟩),
   opAt 500 (.Dup ⟨7, by decide⟩), opAt 501 .MULMOD]

def bitMaskPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 502 (.Dup ⟨1, by decide⟩), pushAt 503 0 0, opAt 504 .SUB]

def bitProductPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 505 (.Dup ⟨9, by decide⟩), opAt 506 (.Dup ⟨9, by decide⟩),
   opAt 507 (.Dup ⟨3, by decide⟩), opAt 508 .MULMOD]

def bitChoosePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 509 (.Dup ⟨2, by decide⟩), opAt 510 .XOR, opAt 511 .AND,
   opAt 512 (.Dup ⟨1, by decide⟩), opAt 513 .XOR]

def bitAdvancePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 514 (.Swap ⟨6, by decide⟩), opAt 515 .POP, opAt 516 .POP,
   opAt 517 .POP, pushAt 518 1 1, opAt 519 (.Dup ⟨1, by decide⟩),
   opAt 520 .ADD, opAt 521 (.Swap ⟨0, by decide⟩), opAt 522 .POP,
   pushAt 523 2 606, opAt 524 .JUMP]

def expOffset (input : ByteArray) : Nat := 96 + baseSize input
def modulusOffset (input : ByteArray) : Nat := expOffset input + exponentSize input

def modulusValue (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input (modulusOffset input) (modulusSize input)

def callerRest (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat (modulusOffset input), UInt256.ofNat (expOffset input),
    UInt256.ofNat (modulusSize input), UInt256.ofNat (exponentSize input),
    UInt256.ofNat (baseSize input)]

def nonzeroState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 538
    stack := [UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1267] ++ callerRest input }

def loadedState (input : ByteArray) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 532
    stack := (538 : UInt256) :: UInt256.ofNat (modulusValue input) ::
      (nonzeroState input).stack }

def zeroDispatchState (input : ByteArray) : State :=
  { nonzeroState input with pc := UInt256.ofNat 533 }

def zeroModulusFinalState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 537
    stack := [UInt256.ofNat 0, UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96, UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input), UInt256.ofNat 1267] ++ callerRest input
    halt := .Returned
    hReturn := MachineState.readPadded ByteArray.empty 6144 (modulusSize input)
    activeWords := (Dispatch.wordEntryState input).activeWordsAfterUInt256
      6144 (modulusSize input) }

def byteWord (input : ByteArray) (offset : Nat) : UInt256 :=
  Accessors.calldataByteValue (Dispatch.wordEntryState input) (UInt256.ofNat offset)

def baseStep (input : ByteArray) (i : Nat) (base : UInt256) : UInt256 :=
  UInt256.addMod
    (UInt256.mulMod base (UInt256.ofNat 256) (UInt256.ofNat (modulusValue input)))
    (byteWord input (96 + i)) (UInt256.ofNat (modulusValue input))

def baseAfter (input : ByteArray) : Nat → UInt256
  | 0 => 0
  | i + 1 => baseStep input i (baseAfter input i)

def baseLoopState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 541
    stack := [UInt256.ofNat i, base, UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1267] ++ callerRest input }

def baseGuardState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  { baseLoopState input i base with pc := UInt256.ofNat 550 }

def baseRest (input : ByteArray) (i : Nat) (base : UInt256) : List UInt256 :=
  [UInt256.ofNat (modulusValue input), UInt256.ofNat i, base,
    UInt256.ofNat (modulusValue input), UInt256.ofNat (baseSize input),
    UInt256.ofNat (exponentSize input), UInt256.ofNat (modulusSize input),
    UInt256.ofNat 96, UInt256.ofNat (expOffset input),
    UInt256.ofNat (modulusOffset input), UInt256.ofNat 1267] ++ callerRest input

def baseCallState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  Accessors.calldataByteEntry (baseLoopState input i base)
    (UInt256.ofNat (96 + i)) 0 562 (baseRest input i base)

def baseReturnedState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  Accessors.calldataByteReturned (baseLoopState input i base)
    (UInt256.ofNat (96 + i)) 562 (baseRest input i base)

def baseFinishDispatchState (input : ByteArray) (base : UInt256) : State :=
  { baseLoopState input (baseSize input) base with pc := UInt256.ofNat 582 }

def expLoopState (input : ByteArray) (i : Nat) (acc base : UInt256) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 589
    stack := [UInt256.ofNat i, acc, base, UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1267] ++ callerRest input }

def expGuardState (input : ByteArray) (i : Nat) (acc base : UInt256) : State :=
  { expLoopState input i acc base with pc := UInt256.ofNat 598 }

def bitLoopState (input : ByteArray) (outer j : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 606
    stack := [UInt256.ofNat j, byte, offset, UInt256.ofNat outer, acc, base,
      UInt256.ofNat (modulusValue input), UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96, UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input), UInt256.ofNat 1267] ++ callerRest input }

def bitGuardState (input : ByteArray) (outer j : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  { bitLoopState input outer j byte offset acc base with pc := UInt256.ofNat 616 }

def exponentBit (byte : UInt256) (j : Nat) : UInt256 :=
  UInt256.land
    (UInt256.shiftRight byte (UInt256.ofNat (7 - j))) (UInt256.ofNat 1)

def bitStep (input : ByteArray) (byte : UInt256) (j : Nat)
    (acc base : UInt256) : UInt256 :=
  let modulus := UInt256.ofNat (modulusValue input)
  let bit := exponentBit byte j
  let square := UInt256.mulMod acc acc modulus
  let product := UInt256.mulMod square base modulus
  let mask := UInt256.ofNat 0 - bit
  UInt256.xor square (UInt256.land (UInt256.xor square product) mask)

def bitDecodedState (input : ByteArray) (outer j : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  { bitLoopState input outer j byte offset acc base with
    pc := UInt256.ofNat 625
    stack := [exponentBit byte j, UInt256.ofNat j, byte, offset,
      UInt256.ofNat outer, acc, base, UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1267] ++ callerRest input }

def bitSelectedState (input : ByteArray) (outer j : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  { bitLoopState input outer j byte offset acc base with
    pc := UInt256.ofNat 641
    stack := [bitStep input byte j acc base,
      UInt256.mulMod acc acc (UInt256.ofNat (modulusValue input)),
      exponentBit byte j, UInt256.ofNat j, byte, offset, UInt256.ofNat outer,
      acc, base, UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1267] ++ callerRest input }

def bitSquaredState (input : ByteArray) (outer j : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  { bitLoopState input outer j byte offset acc base with
    pc := UInt256.ofNat 629
    stack := [UInt256.mulMod acc acc (UInt256.ofNat (modulusValue input)),
      exponentBit byte j, UInt256.ofNat j, byte, offset, UInt256.ofNat outer,
      acc, base, UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1267] ++ callerRest input }

def bitMaskedState (input : ByteArray) (outer j : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  { bitLoopState input outer j byte offset acc base with
    pc := UInt256.ofNat 632
    stack := [UInt256.ofNat 0 - exponentBit byte j,
      UInt256.mulMod acc acc (UInt256.ofNat (modulusValue input)),
      exponentBit byte j, UInt256.ofNat j, byte, offset, UInt256.ofNat outer,
      acc, base, UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1267] ++ callerRest input }

def bitProductState (input : ByteArray) (outer j : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  { bitLoopState input outer j byte offset acc base with
    pc := UInt256.ofNat 636
    stack := [UInt256.mulMod
        (UInt256.mulMod acc acc (UInt256.ofNat (modulusValue input))) base
        (UInt256.ofNat (modulusValue input)),
      UInt256.ofNat 0 - exponentBit byte j,
      UInt256.mulMod acc acc (UInt256.ofNat (modulusValue input)),
      exponentBit byte j, UInt256.ofNat j, byte, offset, UInt256.ofNat outer,
      acc, base, UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1267] ++ callerRest input }

theorem byteWord_eq (input : ByteArray) (offset : Nat)
    (hoffset : offset < 2 ^ 256) :
    byteWord input offset = UInt256.ofNat
      (YulSemantics.EVM.byteFrom input.toList offset).toNat := by
  unfold byteWord Accessors.calldataByteValue
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hoffset]
  change UInt256.byteAt ⟨0⟩ (MachineState.readWord input offset) = _
  exact Challenge.EvmProof.Bytes.byteAt_zero_readWord input offset

theorem baseStep_spec (input : ByteArray) (i modulus : Nat)
    (hmodulus : modulusValue input = modulus) (hmodpos : 0 < modulus)
    (hmodlt : modulus < 2 ^ 256) (hoffset : 96 + i < 2 ^ 256) :
    baseStep input i (UInt256.ofNat
      (Precompile.bytesToNatPadded input 96 i % modulus)) =
      UInt256.ofNat
        (Precompile.bytesToNatPadded input 96 (i + 1) % modulus) := by
  let p := Precompile.bytesToNatPadded input 96 i
  have hbase : p % modulus < modulus := Nat.mod_lt _ hmodpos
  have hbase256 : p % modulus < 2 ^ 256 := hbase.trans hmodlt
  have hbyte := byteWord_eq input (96 + i) hoffset
  have hmword : (UInt256.ofNat modulus).val.val ≠ 0 := by
    change (UInt256.ofNat modulus).toNat ≠ 0
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hmodlt]
    omega
  have hmul : (p % modulus * 256) % modulus < modulus :=
    Nat.mod_lt _ hmodpos
  have hmul256 : (p % modulus * 256) % modulus < 2 ^ 256 :=
    hmul.trans hmodlt
  have hbyte256 :
      (YulSemantics.EVM.byteFrom input.toList (96 + i)).toNat < 2 ^ 256 :=
    (YulSemantics.EVM.byteFrom input.toList (96 + i)).toNat_lt.trans (by norm_num)
  unfold baseStep
  rw [hmodulus, hbyte]
  unfold UInt256.mulMod UInt256.addMod
  rw [if_neg hmword, if_neg hmword]
  simp only [Challenge.EvmProof.Word.word_toNat_ofNat]
  rw [Nat.mod_eq_of_lt hbase256,
    Nat.mod_eq_of_lt (by norm_num : 256 < 2 ^ 256),
    Nat.mod_eq_of_lt hmodlt, Nat.mod_eq_of_lt hmul256,
    Nat.mod_eq_of_lt hbyte256]
  apply congrArg UInt256.ofNat
  rw [Challenge.EvmProof.Bytes.bytesToNatPadded_succ]
  simp [p, Nat.add_mod, Nat.mul_mod]

theorem baseAfter_correct (input : ByteArray) (count : Nat)
    (hmodpos : 0 < modulusValue input)
    (hmodlt : modulusValue input < 2 ^ 256)
    (hbaseSize : baseSize input ≤ 1024)
    (hcount : count ≤ baseSize input) :
    baseAfter input count = UInt256.ofNat
      (Precompile.bytesToNatPadded input 96 count % modulusValue input) := by
  induction count with
  | zero =>
      rw [baseAfter, Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width,
        Nat.zero_mod]
      decide
  | succ count ih =>
      rw [baseAfter, ih (by omega)]
      exact baseStep_spec input count (modulusValue input)
        rfl hmodpos hmodlt (by omega)

@[simp] private theorem startPCs (i : Nat) (hi : 415 ≤ i) (hii : i ≤ 429) :
    Artifact.referenceArtifact.instructionPC i =
      [517, 518, 519, 520, 521, 523, 524, 526, 527, 528, 529, 532,
       533, 534, 537][i - 415]! := by
  interval_cases i <;> decide

@[simp] private theorem jump538 :
    Decode.isValidJumpDest referenceBytecode 538 = true :=
  Artifact.isValidJumpDest_index 430 (by rfl)

@[simp] private theorem wordPCs (i : Nat) (hi : 430 ≤ i) (hii : i ≤ 462) :
    Artifact.referenceArtifact.instructionPC i =
      [538, 539, 540, 541, 542, 543, 544, 545, 546, 549, 550,
       551, 554, 555, 556, 557, 558, 561, 562, 563, 564, 567,
       568, 569, 570, 571, 572, 574, 575, 576, 577, 578, 581][i - 430]! := by
  interval_cases i <;> decide

@[simp] private theorem jump582 :
    Decode.isValidJumpDest referenceBytecode 582 = true :=
  Artifact.isValidJumpDest_index 463 (by rfl)

@[simp] private theorem jump562 :
    Decode.isValidJumpDest referenceBytecode 562 = true :=
  Artifact.isValidJumpDest_index 448 (by rfl)

@[simp] private theorem jump4 :
    Decode.isValidJumpDest referenceBytecode 4 = true :=
  Artifact.isValidJumpDest_index 2 (by rfl)

@[simp] private theorem jump541 :
    Decode.isValidJumpDest referenceBytecode 541 = true :=
  Artifact.isValidJumpDest_index 433 (by rfl)

@[simp] private theorem baseFinishPCs (i : Nat) (hi : 463 ≤ i) (hii : i ≤ 468) :
    Artifact.referenceArtifact.instructionPC i =
      [582, 583, 584, 585, 587, 588][i - 463]! := by
  interval_cases i <;> decide

@[simp] private theorem expPCs (i : Nat) (hi : 469 ≤ i) (hii : i ≤ 535) :
    Artifact.referenceArtifact.instructionPC i =
      [589,590,591,592,593,594,597,598,599,600,601,602,603,604,605,
       606,607,609,610,611,612,615,616,618,619,620,622,623,624,625,
       626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,
       641,642,643,644,645,647,648,649,650,651,654,655,656,657,658,
       659,661,662,663,664,665,668][i - 469]! := by
  interval_cases i <;> decide

@[simp] private theorem jump669 :
    Decode.isValidJumpDest referenceBytecode 669 = true :=
  Artifact.isValidJumpDest_index 536 (by rfl)

@[simp] private theorem jump655 :
    Decode.isValidJumpDest referenceBytecode 655 = true :=
  Artifact.isValidJumpDest_index 525 (by rfl)

@[simp] private theorem jump606 :
    Decode.isValidJumpDest referenceBytecode 606 = true :=
  Artifact.isValidJumpDest_index 484 (by rfl)

@[simp] private theorem jump589 :
    Decode.isValidJumpDest referenceBytecode 589 = true :=
  Artifact.isValidJumpDest_index 469 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_startLoad (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock startLoadPath
      (Dispatch.wordEntryState input) = some (loadedState input) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hword
    (by norm_num : 32 < 2 ^ 256)
  have hshift :
      UInt256.shiftLeft (UInt256.ofNat (32 - modulusSize input))
          (UInt256.ofNat 3) =
        UInt256.ofNat ((32 - modulusSize input) * 8) := by
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat] <;>
      norm_num [Nat.shiftLeft_eq] <;> omega
  have hslice := Challenge.EvmProof.Bytes.shiftRight_readWord input
    (modulusOffset input) (modulusSize input) hmsize hword
  have hmodOff : modulusOffset input < 2 ^ 256 := by
    simp only [modulusOffset, expOffset]
    omega
  have hshiftBound : (32 - modulusSize input) * 2 ^ 3 < 2 ^ 256 := by
    norm_num
    omega
  have hloaded :
      (MachineState.readWord input
        ((96 + baseSize input + exponentSize input) % 2 ^ 256)).shiftRight
          (((32 : UInt256) - UInt256.ofNat (modulusSize input)).shiftLeft 3) =
        UInt256.ofNat (modulusValue input) := by
    change (MachineState.readWord input
      ((modulusOffset input) % 2 ^ 256)).shiftRight _ = _
    rw [Nat.mod_eq_of_lt hmodOff,
      show (32 : UInt256) = UInt256.ofNat 32 by decide, hsub,
      show (3 : UInt256) = UInt256.ofNat 3 by decide, hshift, hslice]
    rfl
  norm_num at hloaded
  simp (config := { maxSteps := 300000 })
    [startLoadPath, startPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Dispatch.wordEntryState, Main.headerState, initialState, loadedState,
      nonzeroState, callerRest,
      expOffset, modulusOffset, startPCs, hsub, hshift, hslice,
      hmodOff, hshiftBound, UInt256.isTrue,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]
  rw [hloaded]
set_option linter.unusedSimpArgs false in
theorem run_startJump_nonzero (input : ByteArray)
    (hmodulus : 0 < modulusValue input)
    (hmodlt : modulusValue input < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runLocatedBlock startJumpPath
      (loadedState input) = some (nonzeroState input) := by
  have hmodNat : modulusValue input % 2 ^ 256 = modulusValue input :=
    Nat.mod_eq_of_lt hmodlt
  have hcondition : modulusValue input % 2 ^ 256 ≠ 0 := by
    rw [hmodNat]
    omega
  have h538 : (538 : UInt256).toNat = 538 := by decide
  have h538Word : (538 : UInt256) = UInt256.ofNat 538 := by decide
  simp [startJumpPath, opAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadedState, nonzeroState, callerRest, Dispatch.wordEntryState,
    Main.headerState, initialState, jump538, UInt256.isTrue,
    Challenge.EvmProof.Word.word_toNat_ofNat, hmodNat, hcondition,
    hmodulus, h538, h538Word, jump538]
  simp_all [hcondition, h538, h538Word, jump538]

set_option linter.unusedSimpArgs false in
theorem run_startJump_zero (input : ByteArray)
    (hmodulus : modulusValue input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock startJumpPath
      (loadedState input) = some (zeroDispatchState input) := by
  simp [startJumpPath, opAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadedState, zeroDispatchState, nonzeroState, callerRest,
    Dispatch.wordEntryState, Main.headerState, initialState,
    UInt256.isTrue, hmodulus,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_zeroTail (input : ByteArray) (hvalid : ValidInput input)
    (hmodulus : modulusValue input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock zeroTailPath
      (zeroDispatchState input) = some (zeroModulusFinalState input) := by
  rcases hvalid with ⟨_, _, _, hm⟩
  have hm' : modulusSize input < 2 ^ 256 := by omega
  have hmmod : modulusSize input % 2 ^ 256 = modulusSize input :=
    Nat.mod_eq_of_lt hm'
  have hmmodLiteral : modulusSize input %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        modulusSize input := by
    exact Nat.mod_eq_of_lt (by norm_num at hm'; exact hm')
  have h6144 : (6144 : UInt256).toNat = 6144 := by decide
  have h0 : (0 : UInt256).toNat = 0 := by decide
  simp [zeroTailPath, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    zeroDispatchState, zeroModulusFinalState, nonzeroState, callerRest,
    Dispatch.wordEntryState, Main.headerState, initialState, startPCs,
    Challenge.EvmProof.Word.word_toNat_ofNat, hmmod, hmmodLiteral,
    Nat.mod_eq_of_lt hm', h6144, h0, hmodulus]
  simp_all [State.activeWordsAfterUInt256, MachineState.activeWordsAfter]

set_option linter.unusedSimpArgs false in
theorem run_baseSetup (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseSetupPath
      (nonzeroState input) = some (baseLoopState input 0 0) := by
  have hzeroWord : UInt256.ofNat 0 = (0 : UInt256) := by decide
  simp (config := { maxSteps := 100000 })
    [baseSetupPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      nonzeroState, baseLoopState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, wordPCs, hzeroWord]
  decide

set_option linter.unusedSimpArgs false in
theorem run_baseGuard (input : ByteArray) (i : Nat) (base : UInt256)
    (hvalid : ValidInput input) (hi : i < baseSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseGuardPath
      (baseLoopState input i base) = some (baseGuardState input i base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hi256 : i < 2 ^ 256 := by omega
  have hb256 : baseSize input < 2 ^ 256 := by omega
  have himod : i % 2 ^ 256 = i := Nat.mod_eq_of_lt hi256
  have hbmod : baseSize input % 2 ^ 256 = baseSize input :=
    Nat.mod_eq_of_lt hb256
  have hilt : i % 2 ^ 256 < baseSize input % 2 ^ 256 := by
    rw [himod, hbmod]
    exact hi
  have hisZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  have hcond :
      (if i % 2 ^ 256 < baseSize input % 2 ^ 256 then UInt256.ofNat 1
        else UInt256.ofNat 0).isZero.toNat = 0 := by
    rw [if_pos hilt]
    exact hisZero
  have hcondLiteral :
      (if i %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 <
          baseSize input %
          115792089237316195423570985008687907853269984665640564039457584007913129639936
        then UInt256.ofNat 1 else UInt256.ofNat 0).isZero.toNat = 0 := by
    exact hcond
  have h550 : (550 : UInt256).toNat = 550 := by decide
  simp (config := { maxSteps := 150000 })
    [baseGuardPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseLoopState, baseGuardState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, wordPCs,
      UInt256.isTrue, UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      hi, hi256, hb256, himod, hbmod, hilt, hisZero, hcond, hcondLiteral,
      h550]

set_option linter.unusedSimpArgs false in
theorem run_baseCall (input : ByteArray) (i : Nat) (base : UInt256)
    (hvalid : ValidInput input) (hi : i < baseSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseCallPath
      (baseGuardState input i base) = some (baseCallState input i base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have h4 : (4 : UInt256).toNat = 4 := by decide
  have h4Word : (4 : UInt256) = UInt256.ofNat 4 := by decide
  have hoff : 96 + i < 2 ^ 256 := by omega
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 96) (by omega : i + 96 < 2 ^ 256)
  have hzeroWord : ({ val := 0 } : UInt256) = 0 := by decide
  simp (config := { maxSteps := 150000 })
    [baseCallPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseGuardState, baseCallState, baseRest, baseLoopState,
      Accessors.calldataByteEntry, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, wordPCs,
      Challenge.EvmProof.Word.word_toNat_ofNat, h4, h4Word, hzeroWord,
      jump4, hoff, hadd]

set_option linter.unusedSimpArgs false in
theorem run_baseTail (input : ByteArray) (i : Nat) (base : UInt256)
    (hvalid : ValidInput input) (hi : i < baseSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseTailPath
      (baseReturnedState input i base) =
        some (baseLoopState input (i + 1) (baseStep input i base)) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hi256 : i < 2 ^ 256 := by omega
  have h562 : (562 : UInt256).toNat = 562 := by decide
  have h562Word : (562 : UInt256) = UInt256.ofNat 562 := by decide
  have h541 : (541 : UInt256).toNat = 541 := by decide
  have h541Word : (541 : UInt256) = UInt256.ofNat 541 := by decide
  have hisucc' := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 1) (by omega : i + 1 < 2 ^ 256)
  have h256Word : (256 : UInt256) = UInt256.ofNat 256 := by decide
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 250000 })
    [baseTailPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseReturnedState, Accessors.calldataByteReturned, baseRest,
      baseLoopState, baseStep, byteWord, Accessors.calldataByteValue,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, wordPCs, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hi256, h562, h562Word, h541, h541Word, h256Word, honeWord, jump541,
      hisucc']

set_option linter.unusedSimpArgs false in
theorem run_baseFinishGuard (input : ByteArray) (base : UInt256)
    (hvalid : ValidInput input) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseGuardPath
      (baseLoopState input (baseSize input) base) =
        some (baseFinishDispatchState input base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hb256 : baseSize input < 2 ^ 256 := by omega
  have hbmod : baseSize input % 2 ^ 256 = baseSize input :=
    Nat.mod_eq_of_lt hb256
  have h582 : (582 : UInt256).toNat = 582 := by decide
  have h582Word : (582 : UInt256) = UInt256.ofNat 582 := by decide
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  simp (config := { maxSteps := 150000 })
    [baseGuardPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseLoopState, baseFinishDispatchState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, wordPCs,
      UInt256.isTrue, UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      hb256, hbmod, hzeroFalse, h582, h582Word, jump582]

set_option linter.unusedSimpArgs false in
theorem run_baseFinishTail (input : ByteArray) (base : UInt256)
    (hvalid : ValidInput input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseFinishTailPath
      (baseFinishDispatchState input base) =
        some (expLoopState input 0
          (UInt256.ofNat 1 % UInt256.ofNat (modulusValue input)) base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hmval : modulusValue input < 2 ^ 256 :=
    (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input
      (modulusOffset input) (modulusSize input)).trans_le (by
        have hp := pow_le_pow_right₀ (by omega : 1 ≤ (256 : Nat)) hword
        exact hp.trans (by norm_num))
  have hzeroWord : UInt256.ofNat 0 = (0 : UInt256) := by decide
  have hzeroRaw : ({ val := 0 } : UInt256) = 0 := by decide
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 150000 })
    [baseFinishTailPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseFinishDispatchState, baseLoopState, expLoopState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, wordPCs,
      baseFinishPCs,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hmval, hzeroWord, hzeroRaw, honeWord]

set_option linter.unusedSimpArgs false in
theorem run_expGuard (input : ByteArray) (i : Nat) (acc base : UInt256)
    (hvalid : ValidInput input) (hi : i < exponentSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock expGuardPath
      (expLoopState input i acc base) = some (expGuardState input i acc base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hi256 : i < 2 ^ 256 := by omega
  have he256 : exponentSize input < 2 ^ 256 := by omega
  have himod : i % 2 ^ 256 = i := Nat.mod_eq_of_lt hi256
  have hemod : exponentSize input % 2 ^ 256 = exponentSize input :=
    Nat.mod_eq_of_lt he256
  have hilt : i % 2 ^ 256 < exponentSize input % 2 ^ 256 := by
    rw [himod, hemod]
    exact hi
  have hiltLiteral :
      i %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 <
        exponentSize input %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num at hilt ⊢
    exact hilt
  have hcondLiteral :
      (if i %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 <
          exponentSize input %
          115792089237316195423570985008687907853269984665640564039457584007913129639936
        then UInt256.ofNat 1 else UInt256.ofNat 0).isZero.toNat = 0 := by
    rw [if_pos hiltLiteral]
    decide
  have h598 : (598 : UInt256).toNat = 598 := by decide
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  simp (config := { maxSteps := 150000 })
    [expGuardPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      expLoopState, expGuardState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, expPCs,
      UInt256.isTrue, UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      hi, hi256, he256, himod, hemod, hilt, hiltLiteral, hcondLiteral,
      honeIsZero, h598]

set_option linter.unusedSimpArgs false in
theorem run_expLoad (input : ByteArray) (i : Nat) (acc base : UInt256)
    (hvalid : ValidInput input) (hi : i < exponentSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock expLoadPath
      (expGuardState input i acc base) =
        some (bitLoopState input i 0 (byteWord input (expOffset input + i))
          (UInt256.ofNat (expOffset input + i)) acc base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hoff : expOffset input + i < 2 ^ 256 := by
    simp only [expOffset]
    omega
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := expOffset input) (b := i) hoff
  have hzeroWord : UInt256.ofNat 0 = (0 : UInt256) := by decide
  have hzeroRaw : ({ val := 0 } : UInt256) = 0 := by decide
  simp (config := { maxSteps := 175000 })
    [expLoadPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      expGuardState, expLoopState, bitLoopState, byteWord,
      Accessors.calldataByteValue,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs, Challenge.EvmProof.Word.word_toNat_ofNat,
      hoff, hadd, hzeroWord, hzeroRaw]

set_option linter.unusedSimpArgs false in
theorem run_bitGuard (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) (hj : j < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitGuardPath
      (bitLoopState input outer j byte offset acc base) =
        some (bitGuardState input outer j byte offset acc base) := by
  have hj256 : j < 2 ^ 256 := by omega
  have hjmod : j % 2 ^ 256 = j := Nat.mod_eq_of_lt hj256
  have h8mod : 8 % 2 ^ 256 = 8 := by norm_num
  have hjlt : j % 2 ^ 256 < 8 % 2 ^ 256 := by
    rw [hjmod, h8mod]
    exact hj
  have hjltLiteral :
      j %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 <
        8 %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num at hjlt ⊢
    exact hjlt
  have hcondLiteral :
      (if j %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 <
          8 %
          115792089237316195423570985008687907853269984665640564039457584007913129639936
        then UInt256.ofNat 1 else UInt256.ofNat 0).isZero.toNat = 0 := by
    rw [if_pos hjltLiteral]
    decide
  have h616 : (616 : UInt256).toNat = 616 := by decide
  have h8 : (8 : UInt256).toNat = 8 := by decide
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  simp (config := { maxSteps := 150000 })
    [bitGuardPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitLoopState, bitGuardState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, expPCs,
      UInt256.isTrue, UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      hj, hj256, hjmod, h8mod, hjlt, hjltLiteral, hcondLiteral,
      h8, honeIsZero, h616]

set_option linter.unusedSimpArgs false in
theorem run_bitDecode (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) (hj : j < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitDecodePath
      (bitGuardState input outer j byte offset acc base) =
        some (bitDecodedState input outer j byte offset acc base) := by
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega : j ≤ 7)
    (by norm_num : 7 < 2 ^ 256)
  have hshift := Challenge.EvmProof.Word.shiftRight_ofNat
    (value := byte.toNat) (shift := 7 - j) byte.val.isLt (by omega)
  have hbyte : UInt256.ofNat byte.toNat = byte := by
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt byte.val.isLt
  have h7Word : (7 : UInt256) = UInt256.ofNat 7 := by decide
  have h1Word : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 175000 })
    [bitDecodePath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitGuardState, bitDecodedState, bitLoopState, exponentBit,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt, hj, hsub, hshift, hbyte, h7Word, h1Word]

set_option linter.unusedSimpArgs false in
theorem run_bitSquare (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitSquarePath
      (bitDecodedState input outer j byte offset acc base) =
        some (bitSquaredState input outer j byte offset acc base) := by
  simp (config := { maxSteps := 125000 })
    [bitSquarePath, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitDecodedState, bitSquaredState, bitLoopState,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_bitMask (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitMaskPath
      (bitSquaredState input outer j byte offset acc base) =
        some (bitMaskedState input outer j byte offset acc base) := by
  have hzeroRaw : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 125000 })
    [bitMaskPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSquaredState, bitMaskedState, bitLoopState,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs, hzeroRaw]

set_option linter.unusedSimpArgs false in
theorem run_bitProduct (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitProductPath
      (bitMaskedState input outer j byte offset acc base) =
        some (bitProductState input outer j byte offset acc base) := by
  simp (config := { maxSteps := 125000 })
    [bitProductPath, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitMaskedState, bitProductState, bitLoopState,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs]

set_option linter.unusedSimpArgs false in
theorem run_bitChoose (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitChoosePath
      (bitProductState input outer j byte offset acc base) =
        some (bitSelectedState input outer j byte offset acc base) := by
  simp (config := { maxSteps := 150000 })
    [bitChoosePath, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitProductState, bitSelectedState, bitLoopState, bitStep,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs]

set_option linter.unusedSimpArgs false in
theorem run_bitAdvance (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) (hj : j < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitAdvancePath
      (bitSelectedState input outer j byte offset acc base) =
        some (bitLoopState input outer (j + 1) byte offset
          (bitStep input byte j acc base) base) := by
  have hsucc' := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := j) (b := 1) (by omega : j + 1 < 2 ^ 256)
  have h606 : (606 : UInt256).toNat = 606 := by decide
  have h606Word : (606 : UInt256) = UInt256.ofNat 606 := by decide
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 175000 })
    [bitAdvancePath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSelectedState, bitLoopState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      expPCs, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hj, hsucc', h606, h606Word, honeWord, jump606]

def gasSteps_start (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodulus : 0 < modulusValue input) :
    Challenge.EvmProof.GasSteps (Dispatch.wordEntryState input)
      (nonzeroState input) := by
  have hmodlt : modulusValue input < 2 ^ 256 :=
    (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input
      (modulusOffset input) (modulusSize input)).trans_le (by
        have hp := pow_le_pow_right₀ (by omega : 1 ≤ (256 : Nat)) hword
        exact hp.trans (by norm_num))
  exact (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka startLoadPath rfl rfl
        (run_startLoad input hvalid hmsize hword) rfl
        deployAddress_not_precompile).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka startJumpPath rfl rfl
        (run_startJump_nonzero input hmodulus hmodlt) rfl
        deployAddress_not_precompile)

def gasSteps_baseSetup (input : ByteArray) :
    Challenge.EvmProof.GasSteps (nonzeroState input)
      (baseLoopState input 0 0) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka baseSetupPath
  · rfl
  · rfl
  · exact run_baseSetup input
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_baseIteration (input : ByteArray) (i : Nat) (base : UInt256)
    (hvalid : ValidInput input) (hi : i < baseSize input) :
    Challenge.EvmProof.GasSteps (baseLoopState input i base)
      (baseLoopState input (i + 1) (baseStep input i base)) := by
  have h562 : (562 : UInt256).toNat = 562 := by decide
  have hcap : (baseRest input i base).length < 1017 := by
    simp [baseRest, callerRest]
  have hjump : Decode.isValidJumpDest referenceBytecode
      (562 : UInt256).toNat = true := by
    rw [h562]
    exact jump562
  exact (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka baseGuardPath rfl rfl
        (run_baseGuard input i base hvalid hi) rfl
        deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka baseCallPath rfl rfl
        (run_baseCall input i base hvalid hi) rfl
        deployAddress_not_precompile).trans <|
    (Accessors.gasSteps_calldataByte (baseLoopState input i base)
      (UInt256.ofNat (96 + i)) 0 562 (baseRest input i base)
      hcap rfl rfl rfl deployAddress_not_precompile hjump).trans <|
    Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka baseTailPath rfl rfl
        (run_baseTail input i base hvalid hi) rfl deployAddress_not_precompile

def gasSteps_baseLoop (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (baseLoopState input 0 0)
      (baseLoopState input (baseSize input) (baseAfter input (baseSize input))) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded (baseSize input)
    (fun i hi => gasSteps_baseIteration input i (baseAfter input i) hvalid hi)

def gasSteps_baseFinish (input : ByteArray) (base : UInt256)
    (hvalid : ValidInput input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.GasSteps (baseLoopState input (baseSize input) base)
      (expLoopState input 0
        (UInt256.ofNat 1 % UInt256.ofNat (modulusValue input)) base) := by
  exact (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka baseGuardPath rfl rfl
        (run_baseFinishGuard input base hvalid) rfl
        deployAddress_not_precompile).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka baseFinishTailPath rfl rfl
        (run_baseFinishTail input base hvalid hword) rfl
        deployAddress_not_precompile)

def gasSteps_zeroModulus (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodulus : modulusValue input = 0) :
    Challenge.EvmProof.GasSteps (Dispatch.wordEntryState input)
      (zeroModulusFinalState input) := by
  exact (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka startLoadPath rfl rfl
        (run_startLoad input hvalid hmsize hword) rfl
        deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka startJumpPath rfl rfl
        (run_startJump_zero input hmodulus) rfl
        deployAddress_not_precompile).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka zeroTailPath rfl rfl
        (run_zeroTail input hvalid hmodulus) rfl deployAddress_not_precompile)

def gasSteps_zeroModulus_total (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodulus : modulusValue input = 0) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (zeroModulusFinalState input) :=
  ((Main.gasSteps_header input hvalid).trans
    (Dispatch.gasSteps_wordEntry input hvalid hmsize hword)).trans
      (gasSteps_zeroModulus input hvalid hmsize hword hmodulus)

@[simp] theorem zeroModulusFinalState_isDone (input : ByteArray) :
    (zeroModulusFinalState input).isDone = true := by
  rfl

theorem zeroModulusFinalState_result (input : ByteArray)
    (hmsize : 0 < modulusSize input) (hmodulus : modulusValue input = 0) :
    (zeroModulusFinalState input).toResult = .returned (spec input) := by
  rw [show (zeroModulusFinalState input).toResult =
      .returned (Precompile.natToBytes 0 (modulusSize input)) by
    simp [zeroModulusFinalState, Algorithm.zeroBytes]]
  have hmodulus' :
      Precompile.bytesToNatPadded input
        (96 + baseSize input + exponentSize input) (modulusSize input) = 0 := by
    simpa [modulusValue, modulusOffset, expOffset, Nat.add_assoc] using hmodulus
  simp [spec, Nat.ne_of_gt hmsize, hmodulus', Precompile.modPow]

end Challenge.Modexp.Reference.Proofs.Bytecode.Word
