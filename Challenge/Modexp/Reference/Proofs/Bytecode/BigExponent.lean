import Challenge.Modexp.Reference.Proofs.Bytecode.BigBaseLoop
import Challenge.Modexp.Reference.Proofs.Bytecode.BigMulGas
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
/-! # Certified multi-limb exponentiation path -/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigExponent

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open BigBase
open BigBaseLoop

private theorem wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.referenceInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.referenceInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def startExponentPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 717 .JUMPDEST, pushAt 718 0 0]

def outerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 719 .JUMPDEST, opAt 720 (.Dup ⟨4, by decide⟩),
   opAt 721 (.Dup ⟨1, by decide⟩), opAt 722 .LT, opAt 723 .ISZERO,
   pushAt 724 2 1118, opAt 725 .JUMPI]

def outerToInnerPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 726 (.Dup ⟨0, by decide⟩), opAt 727 (.Dup ⟨8, by decide⟩),
   opAt 728 .ADD, opAt 729 (.Dup ⟨0, by decide⟩),
   opAt 730 .CALLDATALOAD, pushAt 731 0 0, opAt 732 .BYTE,
   pushAt 733 0 0]

def innerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 734 .JUMPDEST, pushAt 735 1 8, opAt 736 (.Dup ⟨1, by decide⟩),
   opAt 737 .LT, opAt 738 .ISZERO, pushAt 739 2 1104,
   opAt 740 .JUMPI]

def innerToSquarePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [pushAt 741 1 1, opAt 742 (.Dup ⟨2, by decide⟩),
   opAt 743 (.Dup ⟨2, by decide⟩), pushAt 744 1 7,
   opAt 745 .SUB, opAt 746 .SHR, opAt 747 .AND,
   pushAt 748 2 1000, opAt 749 (.Dup ⟨7, by decide⟩),
   pushAt 750 0 0, pushAt 751 2 3072, pushAt 752 2 2048,
   pushAt 753 2 2048, pushAt 754 2 310, opAt 755 .JUMP]

def squareToCopyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 756 .JUMPDEST, pushAt 757 2 1015,
   opAt 758 (.Dup ⟨7, by decide⟩), pushAt 759 2 3072,
   pushAt 760 2 2048, pushAt 761 2 58, opAt 762 .JUMP]

def copyToProductPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 763 .JUMPDEST, pushAt 764 2 1034,
   opAt 765 (.Dup ⟨7, by decide⟩), pushAt 766 0 0,
   pushAt 767 2 3072, pushAt 768 2 1024, pushAt 769 2 2048,
   pushAt 770 2 310, opAt 771 .JUMP]

def productToSelectPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 772 .JUMPDEST, opAt 773 (.Dup ⟨0, by decide⟩),
   pushAt 774 0 0, opAt 775 .SUB, pushAt 776 0 0]

def selectGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 777 .JUMPDEST, opAt 778 (.Dup ⟨8, by decide⟩),
   opAt 779 (.Dup ⟨1, by decide⟩), opAt 780 .LT, opAt 781 .ISZERO,
   pushAt 782 2 1090, opAt 783 .JUMPI]

def selectBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 784 (.Dup ⟨0, by decide⟩), pushAt 785 1 5, opAt 786 .SHL,
   opAt 787 (.Dup ⟨0, by decide⟩), pushAt 788 2 2048, opAt 789 .ADD,
   opAt 790 .MLOAD, opAt 791 (.Dup ⟨1, by decide⟩),
   pushAt 792 2 3072, opAt 793 .ADD, opAt 794 .MLOAD,
   opAt 795 (.Dup ⟨4, by decide⟩), opAt 796 (.Dup ⟨1, by decide⟩),
   opAt 797 (.Dup ⟨3, by decide⟩), opAt 798 .XOR, opAt 799 .AND,
   opAt 800 (.Dup ⟨2, by decide⟩), opAt 801 .XOR,
   opAt 802 (.Dup ⟨3, by decide⟩), pushAt 803 2 2048,
   opAt 804 .ADD, opAt 805 .MSTORE, opAt 806 .POP, opAt 807 .POP,
   opAt 808 .POP, pushAt 809 1 1, opAt 810 (.Dup ⟨1, by decide⟩),
   opAt 811 .ADD, opAt 812 (.Swap ⟨0, by decide⟩), opAt 813 .POP,
   pushAt 814 2 1039, opAt 815 .JUMP]

def selectFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 816 .JUMPDEST, opAt 817 .POP, opAt 818 .POP, opAt 819 .POP,
   pushAt 820 1 1, opAt 821 (.Dup ⟨1, by decide⟩), opAt 822 .ADD,
   opAt 823 (.Swap ⟨0, by decide⟩), opAt 824 .POP,
   pushAt 825 2 963, opAt 826 .JUMP]

def innerFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 827 .JUMPDEST, opAt 828 .POP, opAt 829 .POP, opAt 830 .POP,
   pushAt 831 1 1, opAt 832 (.Dup ⟨1, by decide⟩), opAt 833 .ADD,
   opAt 834 (.Swap ⟨0, by decide⟩), opAt 835 .POP,
   pushAt 836 2 946, opAt 837 .JUMP]

def exponentEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 944
           stack := [accumulatorWord, UInt256.ofNat count, UInt256.ofNat b,
             UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff,
             UInt256.ofNat expOff] ++ rest }

def outerLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 946
           stack := [UInt256.ofNat i, accumulatorWord, UInt256.ofNat count,
             UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
             UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest }

def outerBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (i : Nat) : State :=
  { outerLoop s accumulatorWord count b e m baseOff expOff rest i with
      pc := UInt256.ofNat 955 }

def loadedExponentByte (s : State) (expOff i : Nat) : UInt256 :=
  UInt256.byteAt 0 (MachineState.readWord s.executionEnv.calldata (expOff + i))

def innerLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { s with pc := UInt256.ofNat 963
           stack := [UInt256.ofNat j, byte, offset, UInt256.ofNat i,
             accumulatorWord, UInt256.ofNat count, UInt256.ofNat b,
             UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff,
             UInt256.ofNat expOff] ++ rest }

def innerBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { innerLoop s accumulatorWord count b e m baseOff expOff i offset byte rest j with
      pc := UInt256.ofNat 973 }

def exponentBit (byte : UInt256) (j : Nat) : UInt256 :=
  UInt256.land (UInt256.shiftRight byte (UInt256.ofNat (7 - j))) 1

def bitFrame (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte bit : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [bit, UInt256.ofNat j, byte, offset, UInt256.ofNat i, accumulatorWord,
    UInt256.ofNat count, UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
    UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest

def squareEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  BigMul.mulEntry
    (innerBody s accumulatorWord count b e m baseOff expOff i offset byte rest j)
    2048 2048 3072 0 count 1000
    (bitFrame accumulatorWord count b e m baseOff expOff i j offset byte
      (exponentBit byte j) rest)

def mulResult (s : State) (a b out modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let copied := BigMul.mulAfterCopy s a b out modulus count returnDest rest
  let progress := BigMul.mulOuterProgress copied a b out modulus count
    returnDest rest count
  BigMul.mulReturned progress returnDest rest

@[simp] theorem mulResult_pc (s : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (mulResult s a b out modulus count returnDest rest).pc = returnDest := by
  simp [mulResult, BigMul.mulReturned]

@[simp] theorem mulResult_stack (s : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (mulResult s a b out modulus count returnDest rest).stack = rest := by
  simp [mulResult, BigMul.mulReturned]

@[simp] theorem mulResult_halt (s : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (mulResult s a b out modulus count returnDest rest).halt = s.halt := by
  simp [mulResult, BigMul.mulReturned, BigMul.mulAfterCopy,
    BigMul.mulAfterClear]

@[simp] theorem mulResult_executionEnv (s : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (mulResult s a b out modulus count returnDest rest).executionEnv =
      s.executionEnv := by
  simp [mulResult, BigMul.mulReturned, BigMul.mulAfterCopy,
    BigMul.mulAfterClear]

def squareReturned (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  mulResult
    (innerBody s accumulatorWord count b e m baseOff expOff i offset byte rest j)
    2048 2048 3072 0 count 1000
    (bitFrame accumulatorWord count b e m baseOff expOff i j offset byte
      (exponentBit byte j) rest)

def copiedSquare (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  BigHelpers.copyReturned
    (squareReturned s accumulatorWord count b e m baseOff expOff i j
      offset byte rest)
    2048 3072 count 1015
    (bitFrame accumulatorWord count b e m baseOff expOff i j offset byte
      (exponentBit byte j) rest)

@[simp] theorem squareReturned_pc (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) :
    (squareReturned s accumulatorWord count b e m baseOff expOff i j
      offset byte rest).pc = UInt256.ofNat 1000 := by
  have h1000 : (1000 : UInt256) = UInt256.ofNat 1000 := by decide
  simpa [squareReturned] using h1000

@[simp] theorem squareReturned_stack (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) :
    (squareReturned s accumulatorWord count b e m baseOff expOff i j
      offset byte rest).stack =
        bitFrame accumulatorWord count b e m baseOff expOff i j offset byte
          (exponentBit byte j) rest := by
  simp [squareReturned]

def productReturned (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  mulResult
    (copiedSquare s accumulatorWord count b e m baseOff expOff i j
      offset byte rest)
    2048 1024 3072 0 count 1034
    (bitFrame accumulatorWord count b e m baseOff expOff i j offset byte
      (exponentBit byte j) rest)

@[simp] theorem squareReturned_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) :
    (squareReturned s accumulatorWord count b e m baseOff expOff i j
      offset byte rest).halt = s.halt := by
  simp [squareReturned, innerBody, innerLoop]

@[simp] theorem squareReturned_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (squareReturned s accumulatorWord count b e m baseOff expOff i j
      offset byte rest).executionEnv = s.executionEnv := by
  simp [squareReturned, innerBody, innerLoop]

@[simp] theorem copiedSquare_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) :
    (copiedSquare s accumulatorWord count b e m baseOff expOff i j
      offset byte rest).halt = s.halt := by
  simp [copiedSquare, BigHelpers.copyReturned]

@[simp] theorem copiedSquare_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (copiedSquare s accumulatorWord count b e m baseOff expOff i j
      offset byte rest).executionEnv = s.executionEnv := by
  simp [copiedSquare, BigHelpers.copyReturned]

@[simp] theorem productReturned_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) :
    (productReturned s accumulatorWord count b e m baseOff expOff i j
      offset byte rest).halt = s.halt := by
  simp [productReturned]

@[simp] theorem productReturned_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (productReturned s accumulatorWord count b e m baseOff expOff i j
      offset byte rest).executionEnv = s.executionEnv := by
  simp [productReturned]

def selectMask (byte : UInt256) (j : Nat) : UInt256 :=
  0 - exponentBit byte j

def selectOffset (k : Nat) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat k) (UInt256.ofNat 5)

def selectedWord (memory : ByteArray) (mask : UInt256) (k : Nat) : UInt256 :=
  let offset := selectOffset k
  let square := MachineState.readWord memory (2048 + offset).toNat
  let product := MachineState.readWord memory (3072 + offset).toNat
  UInt256.xor square (UInt256.land (UInt256.xor square product) mask)

def selectMemory (memory : ByteArray) (mask : UInt256) : Nat → ByteArray
  | 0 => memory
  | k + 1 =>
      let before := selectMemory memory mask k
      MachineState.writeBytes before
        (Data.Bytes.natToBytesPadded (selectedWord before mask k).toNat 32)
        (2048 + selectOffset k).toNat

def selectWords (active : UInt256) : Nat → UInt256
  | 0 => active
  | k + 1 =>
      let before := selectWords active k
      let square := UInt256.ofNat (MachineState.activeWordsAfter before.toNat
        (2048 + selectOffset k).toNat 32)
      let product := UInt256.ofNat (MachineState.activeWordsAfter square.toNat
        (3072 + selectOffset k).toNat 32)
      UInt256.ofNat (MachineState.activeWordsAfter product.toNat
        (2048 + selectOffset k).toNat 32)

def selectProgress (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (k : Nat) : State :=
  let returned := productReturned s accumulatorWord count b e m baseOff expOff
    i j offset byte rest
  { returned with
    memory := selectMemory returned.memory (selectMask byte j) k
    activeWords := selectWords returned.activeWords k }

@[simp] theorem selectProgress_zero (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) :
    selectProgress s accumulatorWord count b e m baseOff expOff i j offset
        byte rest 0 =
      productReturned s accumulatorWord count b e m baseOff expOff i j offset
        byte rest := by
  unfold selectProgress
  generalize productReturned s accumulatorWord count b e m baseOff expOff i j
    offset byte rest = returned
  cases returned
  rfl

@[simp] theorem selectProgress_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j k : Nat) (offset byte : UInt256)
    (rest : List UInt256) :
    (selectProgress s accumulatorWord count b e m baseOff expOff i j offset
      byte rest k).halt = s.halt := by
  simp [selectProgress]

@[simp] theorem selectProgress_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j k : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (selectProgress s accumulatorWord count b e m baseOff expOff i j offset
      byte rest k).executionEnv = s.executionEnv := by
  simp [selectProgress]

def selectLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j k : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  { selectProgress s accumulatorWord count b e m baseOff expOff i j
      offset byte rest k with
    pc := UInt256.ofNat 1039
    stack := [UInt256.ofNat k, selectMask byte j, exponentBit byte j,
      UInt256.ofNat j, byte, offset, UInt256.ofNat i, accumulatorWord,
      UInt256.ofNat count, UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest }

def selectBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j k : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  { selectLoop s accumulatorWord count b e m baseOff expOff i j k offset byte
      rest with pc := UInt256.ofNat 1048 }

def selectExit (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  { selectLoop s accumulatorWord count b e m baseOff expOff i j count offset
      byte rest with pc := UInt256.ofNat 1090 }

def afterSelectedBit (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  innerLoop
    (selectProgress s accumulatorWord count b e m baseOff expOff i j offset
      byte rest count)
    accumulatorWord count b e m baseOff expOff i offset byte rest (j + 1)

def innerExit (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  { innerLoop s accumulatorWord count b e m baseOff expOff i offset byte rest 8
      with pc := UInt256.ofNat 1104 }

@[simp] private theorem exponentPCs (i : Nat) (hi : 717 ≤ i) (hii : i ≤ 755) :
    Artifact.referenceArtifact.instructionPC i =
      ([944,945,946,947,948,949,950,951,954,955,956,957,958,959,960,961,
        962,963,964,966,967,968,969,972,973,975,976,977,979,980,981,982,
        985,986,987,990,993,996,999])[i - 717]! := by
  interval_cases i <;> decide

private theorem jump310 :
    Decode.isValidJumpDest referenceBytecode 310 = true :=
  Artifact.isValidJumpDest_index 262 (by rfl)

@[simp] private theorem exponentMidPCs (i : Nat) (hi : 756 ≤ i)
    (hii : i ≤ 776) :
    Artifact.referenceArtifact.instructionPC i =
      ([1000,1001,1004,1005,1008,1011,1014,1015,1016,1019,1020,1021,
        1024,1027,1030,1033,1034,1035,1036,1037,1038])[i - 756]! := by
  interval_cases i <;> decide

private theorem jump58 :
    Decode.isValidJumpDest referenceBytecode 58 = true :=
  Artifact.isValidJumpDest_index 43 (by rfl)

@[simp] private theorem selectPCs (i : Nat) (hi : 777 ≤ i)
    (hii : i ≤ 826) :
    Artifact.referenceArtifact.instructionPC i =
      ([1039,1040,1041,1042,1043,1044,1047,1048,1049,1051,1052,1053,
        1056,1057,1058,1059,1062,1063,1064,1065,1066,1067,1068,1069,
        1070,1071,1072,1075,1076,1077,1078,1079,1080,1082,1083,1084,
        1085,1086,1089,1090,1091,1092,1093,1094,1096,1097,1098,1099,
        1100,1103])[i - 777]! := by
  interval_cases i <;> decide

private theorem jump1039 :
    Decode.isValidJumpDest referenceBytecode 1039 = true :=
  Artifact.isValidJumpDest_index 777 (by rfl)

private theorem jump1090 :
    Decode.isValidJumpDest referenceBytecode 1090 = true :=
  Artifact.isValidJumpDest_index 816 (by rfl)

private theorem jump963 :
    Decode.isValidJumpDest referenceBytecode 963 = true :=
  Artifact.isValidJumpDest_index 734 (by rfl)

@[simp] private theorem innerFinishPCs (i : Nat) (hi : 827 ≤ i)
    (hii : i ≤ 837) :
    Artifact.referenceArtifact.instructionPC i =
      ([1104,1105,1106,1107,1108,1110,1111,1112,1113,1114,1117])[i - 827]! := by
  interval_cases i <;> decide

private theorem jump1104 :
    Decode.isValidJumpDest referenceBytecode 1104 = true :=
  Artifact.isValidJumpDest_index 827 (by rfl)

private theorem jump946 :
    Decode.isValidJumpDest referenceBytecode 946 = true :=
  Artifact.isValidJumpDest_index 719 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_startExponent (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1017) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock startExponentPath
      (exponentEntry s accumulatorWord count b e m baseOff expOff rest) =
      some (outerLoop s accumulatorWord count b e m baseOff expOff rest 0) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp [startExponentPath, opAt, pushAt, wfOp, exponentEntry, outerLoop,
    exponentPCs, hrun, hzero, hc7,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_outerGuard (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1014) (he : e < 2 ^ 256) (hi : i < e)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerGuardPath
      (outerLoop s accumulatorWord count b e m baseOff expOff rest i) =
      some (outerBody s accumulatorWord count b e m baseOff expOff rest i) := by
  have hi256 : i < 2 ^ 256 := hi.trans he
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat e) = 1 := by
    rw [UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt he, if_pos hi]
    decide
  have honeNat : (1 : UInt256).toNat = 1 := by decide
  simp [outerGuardPath, opAt, pushAt, wfOp, outerLoop, outerBody,
    exponentPCs, hrun, hlt, honeNat, hc8, hc9, hc10, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_outerToInner (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1013) (hoff : expOff + i < 2 ^ 256)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerToInnerPath
      (outerBody s accumulatorWord count b e m baseOff expOff rest i) =
      some (innerLoop s accumulatorWord count b e m baseOff expOff i
        (UInt256.ofNat (expOff + i)) (loadedExponentByte s expOff i) rest 0) := by
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := expOff) (by omega)
  have hoffNat : (UInt256.ofNat (expOff + i)).toNat = expOff + i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have h0Word : (0 : UInt256) = UInt256.ofNat 0 := by decide
  simp [outerToInnerPath, opAt, pushAt, wfOp, outerBody, outerLoop,
    innerLoop, loadedExponentByte, exponentPCs, hrun, hadd, hoffNat,
    hzero, h0Word, hc8, hc9, hc10, hc11,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

set_option linter.unusedSimpArgs false in
theorem run_innerGuard (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011) (hj : j < 8)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerGuardPath
      (innerLoop s accumulatorWord count b e m baseOff expOff i offset byte rest j) =
      some (innerBody s accumulatorWord count b e m baseOff expOff i offset byte rest j) := by
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat j) 8 = 1 := by
    have hj256 : j < 2 ^ 256 := by omega
    have h8 : (8 : UInt256).toNat = 8 := by decide
    rw [UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hj256, h8, if_pos hj]
    decide
  have honeNat : (1 : UInt256).toNat = 1 := by decide
  simp [innerGuardPath, opAt, pushAt, wfOp, innerLoop, innerBody,
    exponentPCs, hrun, hlt, honeNat, hc11, hc12, hc13, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_innerToSquare (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1005) (hj : j < 8)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerToSquarePath
      (innerBody s accumulatorWord count b e m baseOff expOff i offset byte rest j) =
      some (squareEntry s accumulatorWord count b e m baseOff expOff i j
        offset byte rest) := by
  have hj7 : j ≤ 7 := by omega
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hj7
    (by norm_num : 7 < 2 ^ 256)
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have h310 : (310 : UInt256).toNat = 310 := by decide
  have h310Word : (310 : UInt256) = UInt256.ofNat 310 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hseven : (7 : UInt256) = UInt256.ofNat 7 := by decide
  simp [innerToSquarePath, opAt, pushAt, wfOp, innerBody, innerLoop,
    squareEntry, BigMul.mulEntry, bitFrame, exponentBit, exponentPCs,
    hcode, hrun, jump310, hsub, h310, h310Word, hzero, hone, hseven,
    hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_squareToCopy (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1005)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock squareToCopyPath
      (squareReturned s accumulatorWord count b e m baseOff expOff i j
        offset byte rest) =
      some (BigHelpers.copyEntry
        (squareReturned s accumulatorWord count b e m baseOff expOff i j
          offset byte rest)
        2048 3072 count 1015
        (bitFrame accumulatorWord count b e m baseOff expOff i j offset byte
          (exponentBit byte j) rest)) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hframe : (bitFrame accumulatorWord count b e m baseOff expOff i j
      offset byte (exponentBit byte j) rest).length < 1024 := by
    simp [bitFrame]
    omega
  have h58 : (58 : UInt256).toNat = 58 := by decide
  have h58Word : (58 : UInt256) = UInt256.ofNat 58 := by decide
  have h1000 : (1000 : UInt256).toNat = 1000 := by decide
  have h1000Word : (1000 : UInt256) = UInt256.ofNat 1000 := by decide
  simp [squareToCopyPath, opAt, pushAt, wfOp,
    BigHelpers.copyEntry, bitFrame, exponentMidPCs, hcode, hrun,
    jump58, h58, h58Word, h1000, h1000Word,
    hc12, hc13, hc14, hc15, hc16, hc17, hframe,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_copyToProduct (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1005)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock copyToProductPath
      (copiedSquare s accumulatorWord count b e m baseOff expOff i j
        offset byte rest) =
      some (BigMul.mulEntry
        (copiedSquare s accumulatorWord count b e m baseOff expOff i j
          offset byte rest)
        2048 1024 3072 0 count 1034
        (bitFrame accumulatorWord count b e m baseOff expOff i j offset byte
          (exponentBit byte j) rest)) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hframe : (bitFrame accumulatorWord count b e m baseOff expOff i j
      offset byte (exponentBit byte j) rest).length < 1024 := by
    simp [bitFrame]
    omega
  have h310 : (310 : UInt256).toNat = 310 := by decide
  have h310Word : (310 : UInt256) = UInt256.ofNat 310 := by decide
  have h1015 : (1015 : UInt256).toNat = 1015 := by decide
  have h1015Word : (1015 : UInt256) = UInt256.ofNat 1015 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  simp [copyToProductPath, opAt, pushAt, wfOp, copiedSquare,
    BigHelpers.copyReturned, BigMul.mulEntry, bitFrame, exponentMidPCs,
    hcode, hrun,
    jump310, h310, h310Word, h1015, h1015Word, hzero,
    hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hframe,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_productToSelect (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1010)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock productToSelectPath
      (productReturned s accumulatorWord count b e m baseOff expOff i j
        offset byte rest) =
      some (selectLoop s accumulatorWord count b e m baseOff expOff i j 0
        offset byte rest) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hframe : (bitFrame accumulatorWord count b e m baseOff expOff i j
      offset byte (exponentBit byte j) rest).length < 1024 := by
    simp [bitFrame]
    omega
  have h1034 : (1034 : UInt256).toNat = 1034 := by decide
  have h1034Word : (1034 : UInt256) = UInt256.ofNat 1034 := by decide
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have h0Word : (0 : UInt256) = UInt256.ofNat 0 := by decide
  simp [productToSelectPath, opAt, pushAt, wfOp, productReturned,
    selectLoop, selectMask,
    bitFrame, exponentMidPCs,
    hrun, h1034, h1034Word, hzero, h0Word, hc12, hc13, hc14, hframe,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_selectGuard (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j k : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1007)
    (hcount : count < 2 ^ 256) (hk : k < count)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectGuardPath
      (selectLoop s accumulatorWord count b e m baseOff expOff i j k offset
        byte rest) =
      some (selectBody s accumulatorWord count b e m baseOff expOff i j k
        offset byte rest) := by
  have hk256 : k < 2 ^ 256 := hk.trans hcount
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat k) (UInt256.ofNat count) = 1 := by
    rw [UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hk256, Nat.mod_eq_of_lt hcount, if_pos hk]
    decide
  have honeNat : (1 : UInt256).toNat = 1 := by decide
  simp [selectGuardPath, opAt, pushAt, wfOp, selectLoop, selectBody,
    selectPCs, hrun, hlt, honeNat, hc14, hc15, hc16, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_selectBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j k : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1004)
    (hk : k + 1 < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectBodyPath
      (selectBody s accumulatorWord count b e m baseOff expOff i j k offset
        byte rest) =
      some (selectLoop s accumulatorWord count b e m baseOff expOff i j
        (k + 1) offset byte rest) := by
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := k) (b := 1) hk
  have h1039 : (1039 : UInt256).toNat = 1039 := by decide
  have h1039Word : (1039 : UInt256) = UInt256.ofNat 1039 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  simp (config := { maxSteps := 300000 })
    [selectBodyPath, opAt, pushAt, wfOp, selectBody, selectLoop,
      selectProgress, selectMemory, selectWords, selectedWord, selectOffset,
      selectMask, selectPCs, hcode, hrun, jump1039, h1039, h1039Word,
      hone, hfive, hinc, hc14, hc15, hc16, hc17, hc18, hc19, hc20,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_selectFinishGuard (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1007)
    (_hcount : count < 2 ^ 256) (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectGuardPath
      (selectLoop s accumulatorWord count b e m baseOff expOff i j count
        offset byte rest) =
      some (selectExit s accumulatorWord count b e m baseOff expOff i j
        offset byte rest) := by
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have h1090 : (1090 : UInt256).toNat = 1090 := by decide
  have h1090Word : (1090 : UInt256) = UInt256.ofNat 1090 := by decide
  simp [selectGuardPath, opAt, pushAt, wfOp, selectLoop, selectExit,
    selectPCs, hcode, hrun, hzeroFalse, h1090, h1090Word, jump1090,
    hc14, hc15, hc16, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_selectFinish (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1007) (hj : j < 8)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectFinishPath
      (selectExit s accumulatorWord count b e m baseOff expOff i j offset byte
        rest) =
      some (afterSelectedBit s accumulatorWord count b e m baseOff expOff i j
        offset byte rest) := by
  have hj256 : j + 1 < 2 ^ 256 := by omega
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := j) (b := 1) hj256
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have h963 : (963 : UInt256).toNat = 963 := by decide
  have h963Word : (963 : UInt256) = UInt256.ofNat 963 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp [selectFinishPath, opAt, pushAt, wfOp, selectExit, selectLoop,
    afterSelectedBit, innerLoop, selectPCs, hcode, hrun, jump963,
    h963, h963Word, hone, hinc, hc11, hc12, hc13, hc14, hc15,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_innerFinishGuard (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerGuardPath
      (innerLoop s accumulatorWord count b e m baseOff expOff i offset byte rest
        8) =
      some (innerExit s accumulatorWord count b e m baseOff expOff i offset byte
        rest) := by
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have h8Nat : (8 : UInt256).toNat = 8 := by decide
  have h1104 : (1104 : UInt256).toNat = 1104 := by decide
  have h1104Word : (1104 : UInt256) = UInt256.ofNat 1104 := by decide
  simp [innerGuardPath, opAt, pushAt, wfOp, innerLoop, innerExit,
    exponentPCs, hcode, hrun, hzeroFalse, h8Nat, h1104, h1104Word, jump1104,
    hc11, hc12, hc13, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_innerFinish (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hi : i + 1 < 2 ^ 256) (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerFinishPath
      (innerExit s accumulatorWord count b e m baseOff expOff i offset byte
        rest) =
      some (outerLoop s accumulatorWord count b e m baseOff expOff rest
        (i + 1)) := by
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 1) hi
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have h946 : (946 : UInt256).toNat = 946 := by decide
  have h946Word : (946 : UInt256) = UInt256.ofNat 946 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp [innerFinishPath, opAt, pushAt, wfOp, innerExit, innerLoop,
    outerLoop, innerFinishPCs, hcode, hrun, jump946, h946, h946Word, hone,
    hinc, hc8, hc9, hc10, hc11, hc12,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, List.exchange]

end Challenge.Modexp.Reference.Proofs.Bytecode.BigExponent
