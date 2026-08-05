import Challenge.EvmProof.Stepper
import Challenge.Sha256.Reference.Proofs.Bytecode.Accessors
import Challenge.Sha256.Reference.Proofs.Bytecode.Functions
set_option warningAsError true
set_option maxRecDepth 20000
/-!
# Direct bytecode trace for the SHA-256 message schedule

Two loops.  The first copies sixteen big-endian words out of the padded message
into the `W` array at `0x320`; the second extends them to sixty-four.  Both are
`JUMPDEST`-headed conditions that jump *into* their bodies when the counter is in
range, the inverted polarity the new backend uses throughout.

The pieces the bodies are built from are certified elsewhere: the inlined
sigma-0 segment and the called `smallSigma1` in `Functions`, and the called
`wSet` in `Accessors`.  `W` lives at `0x320`..`0xb20` and the padded message
starts at `0xb20`, so the schedule's writes never disturb the words it reads —
which is what makes `initialWord` stable across the whole first loop.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.Schedule

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

/-- Address of `W[j]`. -/
def wSlotAddr (j : UInt256) : UInt256 :=
  UInt256.ofNat 800 + UInt256.shiftLeft j (UInt256.ofNat 5)

/-- Address of the `j`-th message word, four bytes apart. -/
def msgWordAddr (msgOff j : UInt256) : UInt256 :=
  msgOff + UInt256.shiftLeft j (UInt256.ofNat 2)

/-- The `j`-th schedule word as the bytecode computes it: load the 32-byte window
at `msgOff + 4j` and take its top four bytes. -/
def initialWord (memory : ByteArray) (msgOff j : UInt256) : UInt256 :=
  UInt256.shiftRight
    (MachineState.readWord memory (msgWordAddr msgOff j).toNat)
    (UInt256.ofNat 224)

@[simp] private theorem pc493 :
    Artifact.referenceArtifact.instructionPC 493 = 1046 := by decide

@[simp] private theorem pc494 :
    Artifact.referenceArtifact.instructionPC 494 = 1047 := by decide

@[simp] private theorem pc495 :
    Artifact.referenceArtifact.instructionPC 495 = 1049 := by decide

@[simp] private theorem pc496 :
    Artifact.referenceArtifact.instructionPC 496 = 1050 := by decide

@[simp] private theorem pc497 :
    Artifact.referenceArtifact.instructionPC 497 = 1051 := by decide

@[simp] private theorem pc498 :
    Artifact.referenceArtifact.instructionPC 498 = 1054 := by decide

@[simp] private theorem pc499 :
    Artifact.referenceArtifact.instructionPC 499 = 1055 := by decide

@[simp] private theorem pc500 :
    Artifact.referenceArtifact.instructionPC 500 = 1056 := by decide

@[simp] private theorem pc501 :
    Artifact.referenceArtifact.instructionPC 501 = 1057 := by decide

@[simp] private theorem pc502 :
    Artifact.referenceArtifact.instructionPC 502 = 1059 := by decide

@[simp] private theorem pc503 :
    Artifact.referenceArtifact.instructionPC 503 = 1062 := by decide

@[simp] private theorem pc504 :
    Artifact.referenceArtifact.instructionPC 504 = 1063 := by decide

@[simp] private theorem pc505 :
    Artifact.referenceArtifact.instructionPC 505 = 1064 := by decide

@[simp] private theorem pc506 :
    Artifact.referenceArtifact.instructionPC 506 = 1067 := by decide

@[simp] private theorem pc507 :
    Artifact.referenceArtifact.instructionPC 507 = 1068 := by decide

@[simp] private theorem pc508 :
    Artifact.referenceArtifact.instructionPC 508 = 1069 := by decide

@[simp] private theorem pc509 :
    Artifact.referenceArtifact.instructionPC 509 = 1070 := by decide

@[simp] private theorem pc510 :
    Artifact.referenceArtifact.instructionPC 510 = 1072 := by decide

@[simp] private theorem pc511 :
    Artifact.referenceArtifact.instructionPC 511 = 1073 := by decide

@[simp] private theorem pc512 :
    Artifact.referenceArtifact.instructionPC 512 = 1074 := by decide

@[simp] private theorem pc513 :
    Artifact.referenceArtifact.instructionPC 513 = 1075 := by decide

@[simp] private theorem pc514 :
    Artifact.referenceArtifact.instructionPC 514 = 1076 := by decide

@[simp] private theorem pc515 :
    Artifact.referenceArtifact.instructionPC 515 = 1078 := by decide

@[simp] private theorem pc516 :
    Artifact.referenceArtifact.instructionPC 516 = 1079 := by decide

@[simp] private theorem pc517 :
    Artifact.referenceArtifact.instructionPC 517 = 1080 := by decide

@[simp] private theorem pc518 :
    Artifact.referenceArtifact.instructionPC 518 = 1082 := by decide

@[simp] private theorem pc519 :
    Artifact.referenceArtifact.instructionPC 519 = 1083 := by decide

@[simp] private theorem pc520 :
    Artifact.referenceArtifact.instructionPC 520 = 1086 := by decide

@[simp] private theorem pc521 :
    Artifact.referenceArtifact.instructionPC 521 = 1087 := by decide

@[simp] private theorem pc522 :
    Artifact.referenceArtifact.instructionPC 522 = 1088 := by decide

@[simp] private theorem pc523 :
    Artifact.referenceArtifact.instructionPC 523 = 1090 := by decide

@[simp] private theorem pc524 :
    Artifact.referenceArtifact.instructionPC 524 = 1091 := by decide

@[simp] private theorem pc525 :
    Artifact.referenceArtifact.instructionPC 525 = 1094 := by decide

@[simp] private theorem pc526 :
    Artifact.referenceArtifact.instructionPC 526 = 1095 := by decide

@[simp] private theorem pc543 :
    Artifact.referenceArtifact.instructionPC 543 = 1125 := by decide

@[simp] private theorem pc544 :
    Artifact.referenceArtifact.instructionPC 544 = 1126 := by decide

@[simp] private theorem toNat1046 : (UInt256.ofNat 1046).toNat = 1046 := by decide
@[simp] private theorem toNat1047 : (UInt256.ofNat 1047).toNat = 1047 := by decide
@[simp] private theorem toNat1049 : (UInt256.ofNat 1049).toNat = 1049 := by decide
@[simp] private theorem toNat1050 : (UInt256.ofNat 1050).toNat = 1050 := by decide
@[simp] private theorem toNat1051 : (UInt256.ofNat 1051).toNat = 1051 := by decide
@[simp] private theorem toNat1054 : (UInt256.ofNat 1054).toNat = 1054 := by decide
@[simp] private theorem toNat1055 : (UInt256.ofNat 1055).toNat = 1055 := by decide
@[simp] private theorem toNat1056 : (UInt256.ofNat 1056).toNat = 1056 := by decide
@[simp] private theorem toNat1057 : (UInt256.ofNat 1057).toNat = 1057 := by decide
@[simp] private theorem toNat1059 : (UInt256.ofNat 1059).toNat = 1059 := by decide
@[simp] private theorem toNat1062 : (UInt256.ofNat 1062).toNat = 1062 := by decide
@[simp] private theorem toNat1063 : (UInt256.ofNat 1063).toNat = 1063 := by decide
@[simp] private theorem toNat1064 : (UInt256.ofNat 1064).toNat = 1064 := by decide
@[simp] private theorem toNat1067 : (UInt256.ofNat 1067).toNat = 1067 := by decide
@[simp] private theorem toNat1068 : (UInt256.ofNat 1068).toNat = 1068 := by decide
@[simp] private theorem toNat1069 : (UInt256.ofNat 1069).toNat = 1069 := by decide
@[simp] private theorem toNat1070 : (UInt256.ofNat 1070).toNat = 1070 := by decide
@[simp] private theorem toNat1072 : (UInt256.ofNat 1072).toNat = 1072 := by decide
@[simp] private theorem toNat1073 : (UInt256.ofNat 1073).toNat = 1073 := by decide
@[simp] private theorem toNat1074 : (UInt256.ofNat 1074).toNat = 1074 := by decide
@[simp] private theorem toNat1075 : (UInt256.ofNat 1075).toNat = 1075 := by decide
@[simp] private theorem toNat1076 : (UInt256.ofNat 1076).toNat = 1076 := by decide
@[simp] private theorem toNat1078 : (UInt256.ofNat 1078).toNat = 1078 := by decide
@[simp] private theorem toNat1079 : (UInt256.ofNat 1079).toNat = 1079 := by decide
@[simp] private theorem toNat1080 : (UInt256.ofNat 1080).toNat = 1080 := by decide
@[simp] private theorem toNat1082 : (UInt256.ofNat 1082).toNat = 1082 := by decide
@[simp] private theorem toNat1083 : (UInt256.ofNat 1083).toNat = 1083 := by decide
@[simp] private theorem toNat1086 : (UInt256.ofNat 1086).toNat = 1086 := by decide
@[simp] private theorem toNat1087 : (UInt256.ofNat 1087).toNat = 1087 := by decide
@[simp] private theorem toNat1088 : (UInt256.ofNat 1088).toNat = 1088 := by decide
@[simp] private theorem toNat1090 : (UInt256.ofNat 1090).toNat = 1090 := by decide
@[simp] private theorem toNat1091 : (UInt256.ofNat 1091).toNat = 1091 := by decide
@[simp] private theorem toNat1094 : (UInt256.ofNat 1094).toNat = 1094 := by decide
@[simp] private theorem toNat1095 : (UInt256.ofNat 1095).toNat = 1095 := by decide
@[simp] private theorem toNat1125 : (UInt256.ofNat 1125).toNat = 1125 := by decide
@[simp] private theorem toNat1126 : (UInt256.ofNat 1126).toNat = 1126 := by decide

@[simp] private theorem next493 : (UInt256.ofNat 1046).succ = UInt256.ofNat 1047 := by decide
@[simp] private theorem next494 : UInt256.ofNat 1047 + UInt256.ofNat 2 = UInt256.ofNat 1049 := by decide
@[simp] private theorem next495 : (UInt256.ofNat 1049).succ = UInt256.ofNat 1050 := by decide
@[simp] private theorem next496 : (UInt256.ofNat 1050).succ = UInt256.ofNat 1051 := by decide
@[simp] private theorem next497 : UInt256.ofNat 1051 + UInt256.ofNat 3 = UInt256.ofNat 1054 := by decide
@[simp] private theorem next498 : (UInt256.ofNat 1054).succ = UInt256.ofNat 1055 := by decide
@[simp] private theorem next499 : (UInt256.ofNat 1055).succ = UInt256.ofNat 1056 := by decide
@[simp] private theorem next500 : (UInt256.ofNat 1056).succ = UInt256.ofNat 1057 := by decide
@[simp] private theorem next501 : UInt256.ofNat 1057 + UInt256.ofNat 2 = UInt256.ofNat 1059 := by decide
@[simp] private theorem next502 : UInt256.ofNat 1059 + UInt256.ofNat 3 = UInt256.ofNat 1062 := by decide
@[simp] private theorem next503 : (UInt256.ofNat 1062).succ = UInt256.ofNat 1063 := by decide
@[simp] private theorem next504 : (UInt256.ofNat 1063).succ = UInt256.ofNat 1064 := by decide
@[simp] private theorem next505 : UInt256.ofNat 1064 + UInt256.ofNat 3 = UInt256.ofNat 1067 := by decide
@[simp] private theorem next506 : (UInt256.ofNat 1067).succ = UInt256.ofNat 1068 := by decide
@[simp] private theorem next507 : (UInt256.ofNat 1068).succ = UInt256.ofNat 1069 := by decide
@[simp] private theorem next508 : (UInt256.ofNat 1069).succ = UInt256.ofNat 1070 := by decide
@[simp] private theorem next509 : UInt256.ofNat 1070 + UInt256.ofNat 2 = UInt256.ofNat 1072 := by decide
@[simp] private theorem next510 : (UInt256.ofNat 1072).succ = UInt256.ofNat 1073 := by decide
@[simp] private theorem next511 : (UInt256.ofNat 1073).succ = UInt256.ofNat 1074 := by decide
@[simp] private theorem next512 : (UInt256.ofNat 1074).succ = UInt256.ofNat 1075 := by decide
@[simp] private theorem next513 : (UInt256.ofNat 1075).succ = UInt256.ofNat 1076 := by decide
@[simp] private theorem next514 : UInt256.ofNat 1076 + UInt256.ofNat 2 = UInt256.ofNat 1078 := by decide
@[simp] private theorem next515 : (UInt256.ofNat 1078).succ = UInt256.ofNat 1079 := by decide
@[simp] private theorem next516 : (UInt256.ofNat 1079).succ = UInt256.ofNat 1080 := by decide
@[simp] private theorem next517 : UInt256.ofNat 1080 + UInt256.ofNat 2 = UInt256.ofNat 1082 := by decide
@[simp] private theorem next518 : (UInt256.ofNat 1082).succ = UInt256.ofNat 1083 := by decide
@[simp] private theorem next519 : UInt256.ofNat 1083 + UInt256.ofNat 3 = UInt256.ofNat 1086 := by decide
@[simp] private theorem next520 : (UInt256.ofNat 1086).succ = UInt256.ofNat 1087 := by decide
@[simp] private theorem next521 : (UInt256.ofNat 1087).succ = UInt256.ofNat 1088 := by decide
@[simp] private theorem next522 : UInt256.ofNat 1088 + UInt256.ofNat 2 = UInt256.ofNat 1090 := by decide
@[simp] private theorem next523 : (UInt256.ofNat 1090).succ = UInt256.ofNat 1091 := by decide
@[simp] private theorem next524 : UInt256.ofNat 1091 + UInt256.ofNat 3 = UInt256.ofNat 1094 := by decide
@[simp] private theorem next525 : (UInt256.ofNat 1094).succ = UInt256.ofNat 1095 := by decide
@[simp] private theorem next543 : (UInt256.ofNat 1125).succ = UInt256.ofNat 1126 := by decide

/-! Jump destinations the two loops target. -/

@[simp] private theorem valid1046 :
    Decode.isValidJumpDest referenceBytecode 1046 = true := by
  rw [← pc493]
  exact Artifact.isValidJumpDest_index 493 (by rfl)

@[simp] private theorem valid1068 :
    Decode.isValidJumpDest referenceBytecode 1068 = true := by
  rw [← pc507]
  exact Artifact.isValidJumpDest_index 507 (by rfl)

@[simp] private theorem valid1095 :
    Decode.isValidJumpDest referenceBytecode 1095 = true := by
  rw [← pc526]
  exact Artifact.isValidJumpDest_index 526 (by rfl)

/-! ### First loop: `W[0..15]` from the message -/

def firstConditionPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨493, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨494, .push ⟨1, by decide⟩ (UInt256.ofNat 16), by rfl, by decide⟩,
   ⟨495, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨496, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨497, .push ⟨2, by decide⟩ (UInt256.ofNat 0x42c), by rfl, by decide⟩,
   ⟨498, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def firstBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨507, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨508, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨509, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨510, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨511, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨512, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨513, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨514, .push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨515, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨516, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨517, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨518, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨519, .push ⟨2, by decide⟩ (UInt256.ofNat 0x320), by rfl, by decide⟩,
   ⟨520, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨521, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨522, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨523, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨524, .push ⟨2, by decide⟩ (UInt256.ofNat 0x416), by rfl, by decide⟩,
   ⟨525, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

/-- The exit: the condition falling through at `j = 16`, then the two pops, the
counter reset to 16, and the jump into the extension loop. -/
def firstExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨493, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨494, .push ⟨1, by decide⟩ (UInt256.ofNat 16), by rfl, by decide⟩,
   ⟨495, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨496, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨497, .push ⟨2, by decide⟩ (UInt256.ofNat 0x42c), by rfl, by decide⟩,
   ⟨498, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨499, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨500, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨501, .push ⟨1, by decide⟩ (UInt256.ofNat 16), by rfl, by decide⟩,
   ⟨502, .push ⟨2, by decide⟩ (UInt256.ofNat 0x447), by rfl, by decide⟩,
   ⟨503, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Memory after the first `j` schedule words have been written.

Each word is read from the memory as it stands when the iteration runs, which is
what the machine does.  `W` at `0x320`..`0xb20` and the message at `0xb20` are
disjoint, so this agrees with reading the original memory throughout — but that
is a separate fact about the offsets, not something the trace needs. -/
def firstMemory (base : ByteArray) (msgOff : UInt256) : Nat → ByteArray
  | 0 => base
  | j + 1 =>
      let prev := firstMemory base msgOff j
      MachineState.writeBytes prev
        (Data.Bytes.natToBytesPadded
          (initialWord prev msgOff (UInt256.ofNat j)).toNat 32)
        (wSlotAddr (UInt256.ofNat j)).toNat

/-- Both the `MLOAD` of the message word and the `MSTORE` of the schedule word
touch memory, so each iteration steps the count twice. -/
def firstActiveWords (s : State) (msgOff : UInt256) : Nat → UInt256
  | 0 => s.activeWords
  | j + 1 =>
      let afterLoad := UInt256.ofNat (MachineState.activeWordsAfter
        (firstActiveWords s msgOff j).toNat
        (msgWordAddr msgOff (UInt256.ofNat j)).toNat 32)
      UInt256.ofNat (MachineState.activeWordsAfter afterLoad.toNat
        (wSlotAddr (UInt256.ofNat j)).toNat 32)

def firstLoopState (s : State) (msgOff : UInt256) (rest : List UInt256)
    (j : Nat) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 493)
    stack := UInt256.ofNat j :: msgOff :: rest
    memory := firstMemory s.memory msgOff j
    activeWords := firstActiveWords s msgOff j }

def firstBodyState (s : State) (msgOff : UInt256) (rest : List UInt256)
    (j : Nat) : State :=
  { firstLoopState s msgOff rest j with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 507) }

@[simp] private theorem firstLoopState_halt (s : State) (msgOff : UInt256)
    (rest : List UInt256) (j : Nat) :
    (firstLoopState s msgOff rest j).halt = s.halt := by rfl
@[simp] private theorem firstLoopState_fork (s : State) (msgOff : UInt256)
    (rest : List UInt256) (j : Nat) :
    (firstLoopState s msgOff rest j).fork = s.fork := by rfl
@[simp] private theorem firstLoopState_code (s : State) (msgOff : UInt256)
    (rest : List UInt256) (j : Nat) :
    (firstLoopState s msgOff rest j).executionEnv.code =
      s.executionEnv.code := by rfl
@[simp] private theorem firstLoopState_pc (s : State) (msgOff : UInt256)
    (rest : List UInt256) (j : Nat) :
    (firstLoopState s msgOff rest j).pc = UInt256.ofNat 1046 := by rfl
@[simp] private theorem firstBodyState_pc (s : State) (msgOff : UInt256)
    (rest : List UInt256) (j : Nat) :
    (firstBodyState s msgOff rest j).pc = UInt256.ofNat 1068 := by rfl

set_option maxHeartbeats 1000000 in
theorem run_firstCondition (s : State) (msgOff : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 16) (hcap : rest.length < 1000)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock firstConditionPath
      (firstLoopState s msgOff rest j) =
        some (firstBodyState s msgOff rest j) := by
  have hj256 : j < 2 ^ 256 := by omega
  have hjWord : (UInt256.ofNat j).toNat = j := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hj256]
  have hlt : UInt256.lt (UInt256.ofNat j) (UInt256.ofNat 16) =
      UInt256.ofNat 1 := by
    simp only [UInt256.lt, hjWord, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num : (16 : Nat) < 2 ^ 256)]
    simp [hj]
  have g1 : rest.length + 1 < 1024 := by omega
  have g2 : rest.length + 1 + 1 < 1024 := by omega
  have g3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have g4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  simp [firstConditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    firstLoopState, firstBodyState, hlt, UInt256.isTrue,
    g2, g3, g4, hrun, hcode]

set_option maxHeartbeats 2000000 in
theorem run_firstBody (s : State) (msgOff : UInt256) (rest : List UInt256)
    (j : Nat) (hj : j < 16) (hcap : rest.length < 1000)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock firstBodyPath
      (firstBodyState s msgOff rest j) =
        some (firstLoopState s msgOff rest (j + 1)) := by
  have hsucc : UInt256.ofNat 1 + UInt256.ofNat j = UInt256.ofNat (j + 1) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have g1 : rest.length + 1 < 1024 := by omega
  have g2 : rest.length + 1 + 1 < 1024 := by omega
  have g3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have g4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have g5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp [firstBodyPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    firstBodyState, firstLoopState, firstMemory, firstActiveWords,
    initialWord, msgWordAddr, wSlotAddr, State.activeWordsAfterUInt256,
    g2, g3, g4, g5, hsucc, hrun, hcode]

def gasSteps_firstCondition (s : State) (msgOff : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 16) (hcap : rest.length < 1000)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (firstLoopState s msgOff rest j)
      (firstBodyState s msgOff rest j) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka firstConditionPath
  · exact hcode
  · exact hfork
  · exact run_firstCondition s msgOff rest j hj hcap hrun hcode
  · exact hrun
  · exact hnp

def gasSteps_firstBody (s : State) (msgOff : UInt256) (rest : List UInt256)
    (j : Nat) (hj : j < 16) (hcap : rest.length < 1000)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (firstBodyState s msgOff rest j)
      (firstLoopState s msgOff rest (j + 1)) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka firstBodyPath
  · exact hcode
  · exact hfork
  · exact run_firstBody s msgOff rest j hj hcap hrun hcode
  · exact hrun
  · exact hnp

/-- One complete iteration of the first loop. -/
def gasSteps_firstIteration (s : State) (msgOff : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 16) (hcap : rest.length < 1000)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (firstLoopState s msgOff rest j)
      (firstLoopState s msgOff rest (j + 1)) :=
  (gasSteps_firstCondition s msgOff rest j hj hcap hrun hcode hfork hnp).trans
    (gasSteps_firstBody s msgOff rest j hj hcap hrun hcode hfork hnp)

/-- All sixteen iterations. -/
def gasSteps_firstLoop (s : State) (msgOff : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (firstLoopState s msgOff rest 0)
      (firstLoopState s msgOff rest 16) :=
  Challenge.EvmProof.GasSteps.iterateBounded (count := 16)
    (I := firstLoopState s msgOff rest)
    (fun j hj => gasSteps_firstIteration s msgOff rest j hj hcap hrun hcode
      hfork hnp)

/-- State the first loop hands to the extension loop: the counter reset to 16,
the message offset dropped. -/
def extensionStart (s : State) (msgOff : UInt256) (rest : List UInt256) : State :=
  { firstLoopState s msgOff rest 16 with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 526)
    stack := UInt256.ofNat 16 :: rest }

set_option maxHeartbeats 1000000 in
theorem run_firstExit (s : State) (msgOff : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock firstExitPath
      (firstLoopState s msgOff rest 16) =
        some (extensionStart s msgOff rest) := by
  have g1 : rest.length + 1 < 1024 := by omega
  have g2 : rest.length + 1 + 1 < 1024 := by omega
  have g3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have g4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have g0 : rest.length < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat 16) (UInt256.ofNat 16) =
      (⟨0⟩ : UInt256) := by decide
  simp [firstExitPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    firstLoopState, extensionStart, hlt, UInt256.isTrue,
    g0, g1, g2, g3, g4, hrun, hcode]

end Challenge.Sha256.Reference.Proofs.Bytecode.Schedule
