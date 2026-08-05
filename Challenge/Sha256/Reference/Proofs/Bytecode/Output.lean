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

def startPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨734, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨735, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨736, .push ⟨2, by decide⟩ (UInt256.ofNat 1413), by rfl, by decide⟩,
   ⟨737, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨738, .push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨739, .push ⟨2, by decide⟩ (UInt256.ofNat 318), by rfl, by decide⟩,
   ⟨740, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setup6Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨741, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨742, .push ⟨2, by decide⟩ (UInt256.ofNat 1424), by rfl, by decide⟩,
   ⟨743, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨744, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩,
   ⟨745, .push ⟨2, by decide⟩ (UInt256.ofNat 318), by rfl, by decide⟩,
   ⟨746, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setup5Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨747, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨748, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨749, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨750, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨751, .push ⟨2, by decide⟩ (UInt256.ofNat 1439), by rfl, by decide⟩,
   ⟨752, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨753, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨754, .push ⟨2, by decide⟩ (UInt256.ofNat 318), by rfl, by decide⟩,
   ⟨755, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setup4Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨756, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨757, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨758, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨759, .push ⟨2, by decide⟩ (UInt256.ofNat 1453), by rfl, by decide⟩,
   ⟨760, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨761, .push ⟨1, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨762, .push ⟨2, by decide⟩ (UInt256.ofNat 318), by rfl, by decide⟩,
   ⟨763, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setup3Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨764, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨765, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨766, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨767, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨768, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨769, .push ⟨2, by decide⟩ (UInt256.ofNat 1469), by rfl, by decide⟩,
   ⟨770, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨771, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨772, .push ⟨2, by decide⟩ (UInt256.ofNat 318), by rfl, by decide⟩,
   ⟨773, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setup2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨774, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨775, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨776, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨777, .push ⟨2, by decide⟩ (UInt256.ofNat 1483), by rfl, by decide⟩,
   ⟨778, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨779, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨780, .push ⟨2, by decide⟩ (UInt256.ofNat 318), by rfl, by decide⟩,
   ⟨781, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setup1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨782, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨783, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨784, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨785, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨786, .push ⟨2, by decide⟩ (UInt256.ofNat 1498), by rfl, by decide⟩,
   ⟨787, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨788, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨789, .push ⟨2, by decide⟩ (UInt256.ofNat 318), by rfl, by decide⟩,
   ⟨790, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setup0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨791, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨792, .push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨793, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨794, .push ⟨2, by decide⟩ (UInt256.ofNat 1511), by rfl, by decide⟩,
   ⟨795, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨796, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨797, .push ⟨2, by decide⟩ (UInt256.ofNat 318), by rfl, by decide⟩,
   ⟨798, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def finishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨799, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨800, .push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨801, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨802, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨803, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨804, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨805, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨806, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨807, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨808, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨809, .op .RETURN, by rfl, wfOp (by decide) trivial rfl⟩]

def hWord (s : State) (i : Nat) : UInt256 :=
  MachineState.readWord s.memory
    (Accessors.slotOffset 288 (UInt256.ofNat i))

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

/-- The exact 256-bit packing expression computed by opcodes 800--804. -/
def digestWord (s : State) : UInt256 :=
  UInt256.lor
    (UInt256.lor
      (UInt256.lor
        (UInt256.shiftLeft (hWord s 0) (UInt256.ofNat 224)) (shifted1 s))
      (pair23 s))
    (lowHalf s)

def outputEntry (s : State) (offset : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1401, stack := offset :: rest }

def afterH7 (s : State) (rest : List UInt256) : State :=
  Accessors.loadReturned s 288 (UInt256.ofNat 7) (UInt256.ofNat 1413) rest

def afterH6 (s : State) (rest : List UInt256) : State :=
  Accessors.loadReturned (afterH7 s rest) 288 (UInt256.ofNat 6)
    (UInt256.ofNat 1424) (hWord s 7 :: rest)

def afterH5 (s : State) (rest : List UInt256) : State :=
  Accessors.loadReturned (afterH6 s rest) 288 (UInt256.ofNat 5)
    (UInt256.ofNat 1439) (pair67 s :: rest)

def afterH4 (s : State) (rest : List UInt256) : State :=
  Accessors.loadReturned (afterH5 s rest) 288 (UInt256.ofNat 4)
    (UInt256.ofNat 1453) (shifted5 s :: pair67 s :: rest)

def afterH3 (s : State) (rest : List UInt256) : State :=
  Accessors.loadReturned (afterH4 s rest) 288 (UInt256.ofNat 3)
    (UInt256.ofNat 1469) (lowHalf s :: rest)

def afterH2 (s : State) (rest : List UInt256) : State :=
  Accessors.loadReturned (afterH3 s rest) 288 (UInt256.ofNat 2)
    (UInt256.ofNat 1483) (shifted3 s :: lowHalf s :: rest)

def afterH1 (s : State) (rest : List UInt256) : State :=
  Accessors.loadReturned (afterH2 s rest) 288 (UInt256.ofNat 1)
    (UInt256.ofNat 1498) (pair23 s :: lowHalf s :: rest)

def afterH0 (s : State) (rest : List UInt256) : State :=
  Accessors.loadReturned (afterH1 s rest) 288 (UInt256.ofNat 0)
    (UInt256.ofNat 1511) (shifted1 s :: pair23 s :: lowHalf s :: rest)

def digestBytes (s : State) : ByteArray :=
  Data.Bytes.natToBytesPadded (digestWord s).toNat 32

def outputResult (s : State) (rest : List UInt256) : State :=
  let loaded := afterH0 s rest
  let storedMemory := MachineState.writeBytes loaded.memory (digestBytes s) 0
  let stored := { loaded with
    pc := UInt256.ofNat 1520
    stack := rest
    memory := storedMemory
    activeWords := loaded.activeWordsAfterUInt256 0 32 }
  { stored with
    pc := UInt256.ofNat 1523
    halt := .Returned
    hReturn := digestBytes s
    stack := rest
    activeWords := stored.activeWordsAfterUInt256 0 32 }

-- Instruction offsets in the final block.  Keeping these as small facts
-- avoids re-evaluating the whole artifact during every symbolic block.
@[simp] private theorem pc734 : Artifact.referenceArtifact.instructionPC 734 = 1401 := by decide
@[simp] private theorem pc735 : Artifact.referenceArtifact.instructionPC 735 = 1402 := by decide
@[simp] private theorem pc736 : Artifact.referenceArtifact.instructionPC 736 = 1403 := by decide
@[simp] private theorem pc737 : Artifact.referenceArtifact.instructionPC 737 = 1406 := by decide
@[simp] private theorem pc738 : Artifact.referenceArtifact.instructionPC 738 = 1407 := by decide
@[simp] private theorem pc739 : Artifact.referenceArtifact.instructionPC 739 = 1409 := by decide
@[simp] private theorem pc740 : Artifact.referenceArtifact.instructionPC 740 = 1412 := by decide
@[simp] private theorem pc741 : Artifact.referenceArtifact.instructionPC 741 = 1413 := by decide
@[simp] private theorem pc742 : Artifact.referenceArtifact.instructionPC 742 = 1414 := by decide
@[simp] private theorem pc743 : Artifact.referenceArtifact.instructionPC 743 = 1417 := by decide
@[simp] private theorem pc744 : Artifact.referenceArtifact.instructionPC 744 = 1418 := by decide
@[simp] private theorem pc745 : Artifact.referenceArtifact.instructionPC 745 = 1420 := by decide
@[simp] private theorem pc746 : Artifact.referenceArtifact.instructionPC 746 = 1423 := by decide
@[simp] private theorem pc747 : Artifact.referenceArtifact.instructionPC 747 = 1424 := by decide
@[simp] private theorem pc748 : Artifact.referenceArtifact.instructionPC 748 = 1425 := by decide
@[simp] private theorem pc749 : Artifact.referenceArtifact.instructionPC 749 = 1427 := by decide
@[simp] private theorem pc750 : Artifact.referenceArtifact.instructionPC 750 = 1428 := by decide
@[simp] private theorem pc751 : Artifact.referenceArtifact.instructionPC 751 = 1429 := by decide
@[simp] private theorem pc752 : Artifact.referenceArtifact.instructionPC 752 = 1432 := by decide
@[simp] private theorem pc753 : Artifact.referenceArtifact.instructionPC 753 = 1433 := by decide
@[simp] private theorem pc754 : Artifact.referenceArtifact.instructionPC 754 = 1435 := by decide
@[simp] private theorem pc755 : Artifact.referenceArtifact.instructionPC 755 = 1438 := by decide
@[simp] private theorem pc756 : Artifact.referenceArtifact.instructionPC 756 = 1439 := by decide
@[simp] private theorem pc757 : Artifact.referenceArtifact.instructionPC 757 = 1440 := by decide
@[simp] private theorem pc758 : Artifact.referenceArtifact.instructionPC 758 = 1442 := by decide
@[simp] private theorem pc759 : Artifact.referenceArtifact.instructionPC 759 = 1443 := by decide
@[simp] private theorem pc760 : Artifact.referenceArtifact.instructionPC 760 = 1446 := by decide
@[simp] private theorem pc761 : Artifact.referenceArtifact.instructionPC 761 = 1447 := by decide
@[simp] private theorem pc762 : Artifact.referenceArtifact.instructionPC 762 = 1449 := by decide
@[simp] private theorem pc763 : Artifact.referenceArtifact.instructionPC 763 = 1452 := by decide
@[simp] private theorem pc764 : Artifact.referenceArtifact.instructionPC 764 = 1453 := by decide
@[simp] private theorem pc765 : Artifact.referenceArtifact.instructionPC 765 = 1454 := by decide
@[simp] private theorem pc766 : Artifact.referenceArtifact.instructionPC 766 = 1456 := by decide
@[simp] private theorem pc767 : Artifact.referenceArtifact.instructionPC 767 = 1457 := by decide
@[simp] private theorem pc768 : Artifact.referenceArtifact.instructionPC 768 = 1458 := by decide
@[simp] private theorem pc769 : Artifact.referenceArtifact.instructionPC 769 = 1459 := by decide
@[simp] private theorem pc770 : Artifact.referenceArtifact.instructionPC 770 = 1462 := by decide
@[simp] private theorem pc771 : Artifact.referenceArtifact.instructionPC 771 = 1463 := by decide
@[simp] private theorem pc772 : Artifact.referenceArtifact.instructionPC 772 = 1465 := by decide
@[simp] private theorem pc773 : Artifact.referenceArtifact.instructionPC 773 = 1468 := by decide
@[simp] private theorem pc774 : Artifact.referenceArtifact.instructionPC 774 = 1469 := by decide
@[simp] private theorem pc775 : Artifact.referenceArtifact.instructionPC 775 = 1470 := by decide
@[simp] private theorem pc776 : Artifact.referenceArtifact.instructionPC 776 = 1472 := by decide
@[simp] private theorem pc777 : Artifact.referenceArtifact.instructionPC 777 = 1473 := by decide
@[simp] private theorem pc778 : Artifact.referenceArtifact.instructionPC 778 = 1476 := by decide
@[simp] private theorem pc779 : Artifact.referenceArtifact.instructionPC 779 = 1477 := by decide
@[simp] private theorem pc780 : Artifact.referenceArtifact.instructionPC 780 = 1479 := by decide
@[simp] private theorem pc781 : Artifact.referenceArtifact.instructionPC 781 = 1482 := by decide
@[simp] private theorem pc782 : Artifact.referenceArtifact.instructionPC 782 = 1483 := by decide
@[simp] private theorem pc783 : Artifact.referenceArtifact.instructionPC 783 = 1484 := by decide
@[simp] private theorem pc784 : Artifact.referenceArtifact.instructionPC 784 = 1486 := by decide
@[simp] private theorem pc785 : Artifact.referenceArtifact.instructionPC 785 = 1487 := by decide
@[simp] private theorem pc786 : Artifact.referenceArtifact.instructionPC 786 = 1488 := by decide
@[simp] private theorem pc787 : Artifact.referenceArtifact.instructionPC 787 = 1491 := by decide
@[simp] private theorem pc788 : Artifact.referenceArtifact.instructionPC 788 = 1492 := by decide
@[simp] private theorem pc789 : Artifact.referenceArtifact.instructionPC 789 = 1494 := by decide
@[simp] private theorem pc790 : Artifact.referenceArtifact.instructionPC 790 = 1497 := by decide
@[simp] private theorem pc791 : Artifact.referenceArtifact.instructionPC 791 = 1498 := by decide
@[simp] private theorem pc792 : Artifact.referenceArtifact.instructionPC 792 = 1499 := by decide
@[simp] private theorem pc793 : Artifact.referenceArtifact.instructionPC 793 = 1501 := by decide
@[simp] private theorem pc794 : Artifact.referenceArtifact.instructionPC 794 = 1502 := by decide
@[simp] private theorem pc795 : Artifact.referenceArtifact.instructionPC 795 = 1505 := by decide
@[simp] private theorem pc796 : Artifact.referenceArtifact.instructionPC 796 = 1506 := by decide
@[simp] private theorem pc797 : Artifact.referenceArtifact.instructionPC 797 = 1507 := by decide
@[simp] private theorem pc798 : Artifact.referenceArtifact.instructionPC 798 = 1510 := by decide
@[simp] private theorem pc799 : Artifact.referenceArtifact.instructionPC 799 = 1511 := by decide
@[simp] private theorem pc800 : Artifact.referenceArtifact.instructionPC 800 = 1512 := by decide
@[simp] private theorem pc801 : Artifact.referenceArtifact.instructionPC 801 = 1514 := by decide
@[simp] private theorem pc802 : Artifact.referenceArtifact.instructionPC 802 = 1515 := by decide
@[simp] private theorem pc803 : Artifact.referenceArtifact.instructionPC 803 = 1516 := by decide
@[simp] private theorem pc804 : Artifact.referenceArtifact.instructionPC 804 = 1517 := by decide
@[simp] private theorem pc805 : Artifact.referenceArtifact.instructionPC 805 = 1518 := by decide
@[simp] private theorem pc806 : Artifact.referenceArtifact.instructionPC 806 = 1519 := by decide
@[simp] private theorem pc807 : Artifact.referenceArtifact.instructionPC 807 = 1520 := by decide
@[simp] private theorem pc808 : Artifact.referenceArtifact.instructionPC 808 = 1522 := by decide
@[simp] private theorem pc809 : Artifact.referenceArtifact.instructionPC 809 = 1523 := by decide

theorem run_start (s : State) (offset : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1019) (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock startPath (outputEntry s offset rest) =
      some (Accessors.loadEntry s 318 (UInt256.ofNat 7) ⟨0⟩
        (UInt256.ofNat 1413) rest) := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 318 = true := by decide
  simp [startPath, outputEntry, Accessors.loadEntry,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, hc0, hc1, hc2, hc3, hc4,
    hcode, hrun, hdest]

theorem run_setup6 (s : State) (h7 : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1018) (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup6Path
      { s with pc := UInt256.ofNat 1413, stack := h7 :: rest } =
      some (Accessors.loadEntry s 318 (UInt256.ofNat 6) ⟨0⟩
        (UInt256.ofNat 1424) (h7 :: rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 318 = true := by decide
  simp [setup6Path, Accessors.loadEntry,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, hc1, hc2, hc3, hc4, hc5,
    hcode, hrun, hdest]

theorem run_setup5 (s : State) (h6 h7 : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup5Path
      { s with pc := UInt256.ofNat 1424, stack := h6 :: h7 :: rest } =
      some (Accessors.loadEntry s 318 (UInt256.ofNat 5) ⟨0⟩
        (UInt256.ofNat 1439)
        (UInt256.lor (UInt256.shiftLeft h6 (UInt256.ofNat 32)) h7 :: rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 318 = true := by decide
  simp [setup5Path, Accessors.loadEntry,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, hc1, hc2, hc3, hc4, hc5,
    hcode, hrun, hdest]

theorem run_setup4 (s : State) (h5 packed67 : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1017)
    (hcode : s.executionEnv.code = referenceBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup4Path
      { s with pc := UInt256.ofNat 1439, stack := h5 :: packed67 :: rest } =
      some (Accessors.loadEntry s 318 (UInt256.ofNat 4) ⟨0⟩
        (UInt256.ofNat 1453)
        (UInt256.shiftLeft h5 (UInt256.ofNat 64) :: packed67 :: rest)) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 318 = true := by decide
  simp [setup4Path, Accessors.loadEntry,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, hc2, hc3, hc4, hc5, hc6,
    hcode, hrun, hdest]

theorem run_setup3 (s : State) (h4 shifted5 packed67 : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup3Path
      { s with pc := UInt256.ofNat 1453, stack := h4 :: shifted5 :: packed67 :: rest } =
      some (Accessors.loadEntry s 318 (UInt256.ofNat 3) ⟨0⟩
        (UInt256.ofNat 1469)
        (UInt256.lor (UInt256.lor
          (UInt256.shiftLeft h4 (UInt256.ofNat 96)) shifted5) packed67 :: rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 318 = true := by decide
  simp [setup3Path, Accessors.loadEntry,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, hc1, hc2, hc3, hc4, hc5, hc6,
    hcode, hrun, hdest]

theorem run_setup2 (s : State) (h3 packedLow : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1017)
    (hcode : s.executionEnv.code = referenceBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup2Path
      { s with pc := UInt256.ofNat 1469, stack := h3 :: packedLow :: rest } =
      some (Accessors.loadEntry s 318 (UInt256.ofNat 2) ⟨0⟩
        (UInt256.ofNat 1483)
        (UInt256.shiftLeft h3 (UInt256.ofNat 128) :: packedLow :: rest)) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 318 = true := by decide
  simp [setup2Path, Accessors.loadEntry,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, hc2, hc3, hc4, hc5, hc6,
    hcode, hrun, hdest]

theorem run_setup1 (s : State) (h2 shifted3 packedLow : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup1Path
      { s with pc := UInt256.ofNat 1483, stack := h2 :: shifted3 :: packedLow :: rest } =
      some (Accessors.loadEntry s 318 (UInt256.ofNat 1) ⟨0⟩
        (UInt256.ofNat 1498)
        (UInt256.lor (UInt256.shiftLeft h2 (UInt256.ofNat 160)) shifted3 ::
          packedLow :: rest)) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 318 = true := by decide
  simp [setup1Path, Accessors.loadEntry,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, hc2, hc3, hc4, hc5, hc6,
    hcode, hrun, hdest]

theorem run_setup0 (s : State) (h1 packed23 packedLow : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup0Path
      { s with pc := UInt256.ofNat 1498, stack := h1 :: packed23 :: packedLow :: rest } =
      some (Accessors.loadEntry s 318 ⟨0⟩ ⟨0⟩
        (UInt256.ofNat 1511)
        (UInt256.shiftLeft h1 (UInt256.ofNat 192) :: packed23 :: packedLow :: rest)) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 318 = true := by decide
  simp [setup0Path, Accessors.loadEntry,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, hc3, hc4, hc5, hc6, hc7,
    hcode, hrun, hdest]

theorem run_finish (s : State) (h0 shifted1 packed23 packedLow : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (_hcode : s.executionEnv.code = referenceBytecode) (hrun : s.halt = .Running) :
    let word := UInt256.lor
      (UInt256.lor (UInt256.lor
        (UInt256.shiftLeft h0 (UInt256.ofNat 224)) shifted1) packed23)
      packedLow
    let bytes := Data.Bytes.natToBytesPadded word.toNat 32
    let storedMemory := MachineState.writeBytes s.memory bytes 0
    let stored := { s with
      pc := UInt256.ofNat 1520
      stack := rest
      memory := storedMemory
      activeWords := s.activeWordsAfterUInt256 0 32 }
    Challenge.EvmProof.Stepper.runLocatedBlock finishPath
      ({ s with
        pc := UInt256.ofNat 1511
        stack := h0 :: shifted1 :: packed23 :: packedLow :: rest }) =
      some { stored with
        pc := UInt256.ofNat 1523
        halt := .Returned
        hReturn := bytes
        stack := rest
        activeWords := stored.activeWordsAfterUInt256 0 32 } := by
  dsimp only
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  let word := UInt256.lor
    (UInt256.lor
      (UInt256.lor (UInt256.shiftLeft h0 (UInt256.ofNat 224)) shifted1)
      packed23) packedLow
  let bytes := Data.Bytes.natToBytesPadded word.toNat 32
  have hsize : bytes.size = 32 := by
    simp [bytes, Data.Bytes.natToBytesPadded, ByteArray.size]
  have hread := Challenge.EvmProof.Memory.readPadded_writeBytes_same s.memory bytes 0
  rw [hsize] at hread
  have hz : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have h32 : (UInt256.ofNat 32).toNat = 32 := by decide
  simp [finishPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5,
    hrun, hread, hz, h32, word, bytes]

/-- The final output block returns exactly the 32-byte big-endian packing of
the eight words stored in H slots 0 through 7. -/
def gasSteps_output (s : State) (offset : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (outputEntry s offset rest) (outputResult s rest) := by
  let q7 := afterH7 s rest
  let q6 := afterH6 s rest
  let q5 := afterH5 s rest
  let q4 := afterH4 s rest
  let q3 := afterH3 s rest
  let q2 := afterH2 s rest
  let q1 := afterH1 s rest
  let q0 := afterH0 s rest
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  have valid1413 : Decode.isValidJumpDest referenceBytecode 1413 = true := by
    simpa [Artifact.instructionPC] using Artifact.isValidJumpDest_index 741 (by rfl)
  have valid1424 : Decode.isValidJumpDest referenceBytecode 1424 = true := by
    simpa [Artifact.instructionPC] using Artifact.isValidJumpDest_index 747 (by rfl)
  have valid1439 : Decode.isValidJumpDest referenceBytecode 1439 = true := by
    simpa [Artifact.instructionPC] using Artifact.isValidJumpDest_index 756 (by rfl)
  have valid1453 : Decode.isValidJumpDest referenceBytecode 1453 = true := by
    simpa [Artifact.instructionPC] using Artifact.isValidJumpDest_index 764 (by rfl)
  have valid1469 : Decode.isValidJumpDest referenceBytecode 1469 = true := by
    simpa [Artifact.instructionPC] using Artifact.isValidJumpDest_index 774 (by rfl)
  have valid1483 : Decode.isValidJumpDest referenceBytecode 1483 = true := by
    simpa [Artifact.instructionPC] using Artifact.isValidJumpDest_index 782 (by rfl)
  have valid1498 : Decode.isValidJumpDest referenceBytecode 1498 = true := by
    simpa [Artifact.instructionPC] using Artifact.isValidJumpDest_index 791 (by rfl)
  have valid1511 : Decode.isValidJumpDest referenceBytecode 1511 = true := by
    simpa [Artifact.instructionPC] using Artifact.isValidJumpDest_index 799 (by rfl)
  have gStart : Challenge.EvmProof.GasSteps (outputEntry s offset rest)
      (Accessors.loadEntry s 318 (UInt256.ofNat 7) ⟨0⟩
        (UInt256.ofNat 1413) rest) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka startPath
    · exact hcode
    · exact hfork
    · exact run_start s offset rest (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have gH7 : Challenge.EvmProof.GasSteps
      (Accessors.loadEntry s 318 (UInt256.ofNat 7) ⟨0⟩
        (UInt256.ofNat 1413) rest) q7 := by
    exact Challenge.EvmProof.GasSteps.cast
      (Accessors.gasSteps_hAt s (UInt256.ofNat 7) ⟨0⟩
        (UInt256.ofNat 1413) rest (by omega)
        hcode hfork hrun hnp valid1413)
      rfl (by simp [q7, afterH7])
  have q7code : q7.executionEnv.code = referenceBytecode := by
    simp [q7, afterH7, Accessors.loadReturned, hcode]
  have q7fork : q7.fork = .Osaka := by
    change q7.executionEnv.fork = .Osaka
    simp [q7, afterH7, Accessors.loadReturned, hfork]
  have q7run : q7.halt = .Running := by
    simp [q7, afterH7, Accessors.loadReturned, hrun]
  have q7np : Precompile.isPrecompileWithConfig q7.executionEnv.precompileConfig q7.executionEnv.fork
      q7.executionEnv.codeAddr = false := by
    simpa [q7, afterH7, Accessors.loadReturned] using hnp
  have gSetup6 : Challenge.EvmProof.GasSteps q7
      (Accessors.loadEntry q7 318 (UInt256.ofNat 6) ⟨0⟩
        (UInt256.ofNat 1424) (hWord s 7 :: rest)) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setup6Path q7code q7fork
    · simpa [q7, afterH7, hWord, Accessors.loadReturned] using
        run_setup6 q7 (hWord s 7) rest (by omega) q7code q7run
    · exact q7run
    · exact q7np
  have gH6 : Challenge.EvmProof.GasSteps
      (Accessors.loadEntry q7 318 (UInt256.ofNat 6) ⟨0⟩
        (UInt256.ofNat 1424) (hWord s 7 :: rest)) q6 := by
    exact Challenge.EvmProof.GasSteps.cast
      (Accessors.gasSteps_hAt q7 (UInt256.ofNat 6) ⟨0⟩
        (UInt256.ofNat 1424) (hWord s 7 :: rest)
        (by simp; omega) q7code q7fork q7run q7np valid1424)
      rfl (by simp [q6, afterH6, q7])
  have q6code : q6.executionEnv.code = referenceBytecode := by
    simp [q6, afterH6, q7, afterH7, Accessors.loadReturned, hcode]
  have q6fork : q6.fork = .Osaka := by
    change q6.executionEnv.fork = .Osaka
    simp [q6, afterH6, q7, afterH7, Accessors.loadReturned, hfork]
  have q6run : q6.halt = .Running := by
    simp [q6, afterH6, q7, afterH7, Accessors.loadReturned, hrun]
  have q6np : Precompile.isPrecompileWithConfig q6.executionEnv.precompileConfig q6.executionEnv.fork
      q6.executionEnv.codeAddr = false := by
    simpa [q6, afterH6, q7, afterH7, Accessors.loadReturned] using hnp
  have gSetup5 : Challenge.EvmProof.GasSteps q6
      (Accessors.loadEntry q6 318 (UInt256.ofNat 5) ⟨0⟩
        (UInt256.ofNat 1439) (pair67 s :: rest)) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setup5Path q6code q6fork
    · simpa [q6, afterH6, q7, afterH7, hWord, pair67,
        Accessors.loadReturned] using
        run_setup5 q6 (hWord s 6) (hWord s 7) rest
          (by omega) q6code q6run
    · exact q6run
    · exact q6np
  have gH5 : Challenge.EvmProof.GasSteps
      (Accessors.loadEntry q6 318 (UInt256.ofNat 5) ⟨0⟩
        (UInt256.ofNat 1439) (pair67 s :: rest)) q5 := by
    exact Challenge.EvmProof.GasSteps.cast
      (Accessors.gasSteps_hAt q6 (UInt256.ofNat 5) ⟨0⟩
        (UInt256.ofNat 1439) (pair67 s :: rest)
        (by simp; omega) q6code q6fork q6run q6np valid1439)
      rfl (by simp [q5, afterH5, q6])
  have q5code : q5.executionEnv.code = referenceBytecode := by
    simp [q5, afterH5, q6, afterH6, q7, afterH7,
      Accessors.loadReturned, hcode]
  have q5fork : q5.fork = .Osaka := by
    change q5.executionEnv.fork = .Osaka
    simp [q5, afterH5, q6, afterH6, q7, afterH7,
      Accessors.loadReturned, hfork]
  have q5run : q5.halt = .Running := by
    simp [q5, afterH5, q6, afterH6, q7, afterH7,
      Accessors.loadReturned, hrun]
  have q5np : Precompile.isPrecompileWithConfig q5.executionEnv.precompileConfig q5.executionEnv.fork
      q5.executionEnv.codeAddr = false := by
    simpa [q5, afterH5, q6, afterH6, q7, afterH7,
      Accessors.loadReturned] using hnp
  have gSetup4 : Challenge.EvmProof.GasSteps q5
      (Accessors.loadEntry q5 318 (UInt256.ofNat 4) ⟨0⟩
        (UInt256.ofNat 1453) (shifted5 s :: pair67 s :: rest)) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setup4Path q5code q5fork
    · simpa [q5, afterH5, q6, afterH6, q7, afterH7, hWord, shifted5,
        pair67, Accessors.loadReturned] using
        run_setup4 q5 (hWord s 5) (pair67 s) rest
          (by omega) q5code q5run
    · exact q5run
    · exact q5np
  have gH4 : Challenge.EvmProof.GasSteps
      (Accessors.loadEntry q5 318 (UInt256.ofNat 4) ⟨0⟩
        (UInt256.ofNat 1453) (shifted5 s :: pair67 s :: rest)) q4 := by
    exact Challenge.EvmProof.GasSteps.cast
      (Accessors.gasSteps_hAt q5 (UInt256.ofNat 4) ⟨0⟩
        (UInt256.ofNat 1453) (shifted5 s :: pair67 s :: rest)
        (by simp; omega) q5code q5fork q5run q5np valid1453)
      rfl (by simp [q4, afterH4, q5])
  have q4code : q4.executionEnv.code = referenceBytecode := by
    simp [q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7,
      Accessors.loadReturned, hcode]
  have q4fork : q4.fork = .Osaka := by
    change q4.executionEnv.fork = .Osaka
    simp [q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7,
      Accessors.loadReturned, hfork]
  have q4run : q4.halt = .Running := by
    simp [q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7,
      Accessors.loadReturned, hrun]
  have q4np : Precompile.isPrecompileWithConfig q4.executionEnv.precompileConfig q4.executionEnv.fork
      q4.executionEnv.codeAddr = false := by
    simpa [q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7,
      Accessors.loadReturned] using hnp
  have gSetup3 : Challenge.EvmProof.GasSteps q4
      (Accessors.loadEntry q4 318 (UInt256.ofNat 3) ⟨0⟩
        (UInt256.ofNat 1469) (lowHalf s :: rest)) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setup3Path q4code q4fork
    · simpa [q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7,
        hWord, shifted5, pair67, pair45, lowHalf, Accessors.loadReturned] using
        run_setup3 q4 (hWord s 4) (shifted5 s) (pair67 s) rest
          (by omega) q4code q4run
    · exact q4run
    · exact q4np
  have gH3 : Challenge.EvmProof.GasSteps
      (Accessors.loadEntry q4 318 (UInt256.ofNat 3) ⟨0⟩
        (UInt256.ofNat 1469) (lowHalf s :: rest)) q3 := by
    exact Challenge.EvmProof.GasSteps.cast
      (Accessors.gasSteps_hAt q4 (UInt256.ofNat 3) ⟨0⟩
        (UInt256.ofNat 1469) (lowHalf s :: rest)
        (by simp; omega) q4code q4fork q4run q4np valid1469)
      rfl (by simp [q3, afterH3, q4])
  have q3code : q3.executionEnv.code = referenceBytecode := by
    simp [q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6,
      q7, afterH7, Accessors.loadReturned, hcode]
  have q3fork : q3.fork = .Osaka := by
    change q3.executionEnv.fork = .Osaka
    simp [q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6,
      q7, afterH7, Accessors.loadReturned, hfork]
  have q3run : q3.halt = .Running := by
    simp [q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6,
      q7, afterH7, Accessors.loadReturned, hrun]
  have q3np : Precompile.isPrecompileWithConfig q3.executionEnv.precompileConfig q3.executionEnv.fork
      q3.executionEnv.codeAddr = false := by
    simpa [q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6,
      q7, afterH7, Accessors.loadReturned] using hnp
  have gSetup2 : Challenge.EvmProof.GasSteps q3
      (Accessors.loadEntry q3 318 (UInt256.ofNat 2) ⟨0⟩
        (UInt256.ofNat 1483) (shifted3 s :: lowHalf s :: rest)) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setup2Path q3code q3fork
    · simpa [q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6,
        q7, afterH7, hWord, shifted3, Accessors.loadReturned] using
        run_setup2 q3 (hWord s 3) (lowHalf s) rest
          (by omega) q3code q3run
    · exact q3run
    · exact q3np
  have gH2 : Challenge.EvmProof.GasSteps
      (Accessors.loadEntry q3 318 (UInt256.ofNat 2) ⟨0⟩
        (UInt256.ofNat 1483) (shifted3 s :: lowHalf s :: rest)) q2 := by
    exact Challenge.EvmProof.GasSteps.cast
      (Accessors.gasSteps_hAt q3 (UInt256.ofNat 2) ⟨0⟩
        (UInt256.ofNat 1483) (shifted3 s :: lowHalf s :: rest)
        (by simp; omega) q3code q3fork q3run q3np valid1483)
      rfl (by simp [q2, afterH2, q3])
  have q2code : q2.executionEnv.code = referenceBytecode := by
    simp [q2, afterH2, q3, afterH3, q4, afterH4, q5, afterH5,
      q6, afterH6, q7, afterH7, Accessors.loadReturned, hcode]
  have q2fork : q2.fork = .Osaka := by
    change q2.executionEnv.fork = .Osaka
    simp [q2, afterH2, q3, afterH3, q4, afterH4, q5, afterH5,
      q6, afterH6, q7, afterH7, Accessors.loadReturned, hfork]
  have q2run : q2.halt = .Running := by
    simp [q2, afterH2, q3, afterH3, q4, afterH4, q5, afterH5,
      q6, afterH6, q7, afterH7, Accessors.loadReturned, hrun]
  have q2np : Precompile.isPrecompileWithConfig q2.executionEnv.precompileConfig q2.executionEnv.fork
      q2.executionEnv.codeAddr = false := by
    simpa [q2, afterH2, q3, afterH3, q4, afterH4, q5, afterH5,
      q6, afterH6, q7, afterH7, Accessors.loadReturned] using hnp
  have gSetup1 : Challenge.EvmProof.GasSteps q2
      (Accessors.loadEntry q2 318 (UInt256.ofNat 1) ⟨0⟩
        (UInt256.ofNat 1498) (pair23 s :: lowHalf s :: rest)) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setup1Path q2code q2fork
    · simpa [q2, afterH2, q3, afterH3, q4, afterH4, q5, afterH5,
        q6, afterH6, q7, afterH7, hWord, shifted3, pair23,
        Accessors.loadReturned] using
        run_setup1 q2 (hWord s 2) (shifted3 s) (lowHalf s) rest
          (by omega) q2code q2run
    · exact q2run
    · exact q2np
  have gH1 : Challenge.EvmProof.GasSteps
      (Accessors.loadEntry q2 318 (UInt256.ofNat 1) ⟨0⟩
        (UInt256.ofNat 1498) (pair23 s :: lowHalf s :: rest)) q1 := by
    exact Challenge.EvmProof.GasSteps.cast
      (Accessors.gasSteps_hAt q2 (UInt256.ofNat 1) ⟨0⟩
        (UInt256.ofNat 1498) (pair23 s :: lowHalf s :: rest)
        (by simp; omega) q2code q2fork q2run q2np valid1498)
      rfl (by simp [q1, afterH1, q2])
  have q1code : q1.executionEnv.code = referenceBytecode := by
    simp [q1, afterH1, q2, afterH2, q3, afterH3, q4, afterH4,
      q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned, hcode]
  have q1fork : q1.fork = .Osaka := by
    change q1.executionEnv.fork = .Osaka
    simp [q1, afterH1, q2, afterH2, q3, afterH3, q4, afterH4,
      q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned, hfork]
  have q1run : q1.halt = .Running := by
    simp [q1, afterH1, q2, afterH2, q3, afterH3, q4, afterH4,
      q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned, hrun]
  have q1np : Precompile.isPrecompileWithConfig q1.executionEnv.precompileConfig q1.executionEnv.fork
      q1.executionEnv.codeAddr = false := by
    simpa [q1, afterH1, q2, afterH2, q3, afterH3, q4, afterH4,
      q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hnp
  have gSetup0 : Challenge.EvmProof.GasSteps q1
      (Accessors.loadEntry q1 318 (UInt256.ofNat 0) ⟨0⟩ (UInt256.ofNat 1511)
        (shifted1 s :: pair23 s :: lowHalf s :: rest)) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setup0Path q1code q1fork
    · simpa [q1, afterH1, q2, afterH2, q3, afterH3, q4, afterH4,
        q5, afterH5, q6, afterH6, q7, afterH7, hWord, shifted1, hzero,
        Accessors.loadReturned] using
        run_setup0 q1 (hWord s 1) (pair23 s) (lowHalf s) rest
          (by omega) q1code q1run
    · exact q1run
    · exact q1np
  have gH0 : Challenge.EvmProof.GasSteps
      (Accessors.loadEntry q1 318 (UInt256.ofNat 0) ⟨0⟩ (UInt256.ofNat 1511)
        (shifted1 s :: pair23 s :: lowHalf s :: rest)) q0 := by
    exact Challenge.EvmProof.GasSteps.cast
      (Accessors.gasSteps_hAt q1 (UInt256.ofNat 0) ⟨0⟩
        (UInt256.ofNat 1511) (shifted1 s :: pair23 s :: lowHalf s :: rest)
        (by simp; omega) q1code q1fork q1run q1np valid1511)
      rfl (by simp [q0, afterH0, q1])
  have q0code : q0.executionEnv.code = referenceBytecode := by
    simp [q0, afterH0, q1, afterH1, q2, afterH2, q3, afterH3,
      q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7,
      Accessors.loadReturned, hcode]
  have q0fork : q0.fork = .Osaka := by
    change q0.executionEnv.fork = .Osaka
    simp [q0, afterH0, q1, afterH1, q2, afterH2, q3, afterH3,
      q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7,
      Accessors.loadReturned, hfork]
  have q0run : q0.halt = .Running := by
    simp [q0, afterH0, q1, afterH1, q2, afterH2, q3, afterH3,
      q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7,
      Accessors.loadReturned, hrun]
  have q0np : Precompile.isPrecompileWithConfig q0.executionEnv.precompileConfig q0.executionEnv.fork
      q0.executionEnv.codeAddr = false := by
    simpa [q0, afterH0, q1, afterH1, q2, afterH2, q3, afterH3,
      q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7,
      Accessors.loadReturned] using hnp
  have gFinish : Challenge.EvmProof.GasSteps q0 (outputResult s rest) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka finishPath q0code q0fork
    · simpa [q0, outputResult, afterH0, q1, afterH1, q2, afterH2,
        q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6,
        q7, afterH7, hWord, shifted1, pair23, lowHalf, digestWord,
        digestBytes, Accessors.loadReturned] using
        run_finish q0 (hWord s 0) (shifted1 s) (pair23 s) (lowHalf s)
          rest (by omega) q0code q0run
    · exact q0run
    · exact q0np
  have g1 := gStart.trans gH7
  have g2 := g1.trans gSetup6
  have g3 := g2.trans gH6
  have g4 := g3.trans gSetup5
  have g5 := g4.trans gH5
  have g6 := g5.trans gSetup4
  have g7 := g6.trans gH4
  have g8 := g7.trans gSetup3
  have g9 := g8.trans gH3
  have g10 := g9.trans gSetup2
  have g11 := g10.trans gH2
  have g12 := g11.trans gSetup1
  have g13 := g12.trans gH1
  have g14 := g13.trans gSetup0
  have g15 := g14.trans gH0
  exact g15.trans gFinish

@[simp] theorem outputResult_halt (s : State) (rest : List UInt256) :
    (outputResult s rest).halt = .Returned := by
  simp [outputResult]

@[simp] theorem outputResult_returnData (s : State) (rest : List UInt256) :
    (outputResult s rest).hReturn = digestBytes s := by
  simp [outputResult]

@[simp] theorem outputResult_memory (s : State) (rest : List UInt256) :
    (outputResult s rest).memory =
      MachineState.writeBytes s.memory (digestBytes s) 0 := by
  rfl

/-- The exact memory window consumed by the terminal `RETURN`. -/
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
