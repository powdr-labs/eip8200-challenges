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

/-! ### Second loop: extending `W[16..63]`

Each iteration reads `W[k-16]`, `W[k-15]`, `W[k-7]` and `W[k-2]`, applies the
inlined sigma-0 to `W[k-15]` and the called `smallSigma1` to `W[k-2]`, sums the
four terms modulo 2^32, and writes the result through the called `wSet`.  Its body
therefore splits at the two calls into four straight segments.
-/

@[simp] private theorem pc527 :
    Artifact.referenceArtifact.instructionPC 527 = 1096 := by decide

@[simp] private theorem pc528 :
    Artifact.referenceArtifact.instructionPC 528 = 1098 := by decide

@[simp] private theorem pc529 :
    Artifact.referenceArtifact.instructionPC 529 = 1099 := by decide

@[simp] private theorem pc530 :
    Artifact.referenceArtifact.instructionPC 530 = 1100 := by decide

@[simp] private theorem pc531 :
    Artifact.referenceArtifact.instructionPC 531 = 1103 := by decide

@[simp] private theorem pc532 :
    Artifact.referenceArtifact.instructionPC 532 = 1104 := by decide

@[simp] private theorem pc533 :
    Artifact.referenceArtifact.instructionPC 533 = 1105 := by decide

@[simp] private theorem pc534 :
    Artifact.referenceArtifact.instructionPC 534 = 1108 := by decide

@[simp] private theorem pc535 :
    Artifact.referenceArtifact.instructionPC 535 = 1111 := by decide

@[simp] private theorem pc536 :
    Artifact.referenceArtifact.instructionPC 536 = 1114 := by decide

@[simp] private theorem pc537 :
    Artifact.referenceArtifact.instructionPC 537 = 1115 := by decide

@[simp] private theorem pc538 :
    Artifact.referenceArtifact.instructionPC 538 = 1116 := by decide

@[simp] private theorem pc539 :
    Artifact.referenceArtifact.instructionPC 539 = 1119 := by decide

@[simp] private theorem pc540 :
    Artifact.referenceArtifact.instructionPC 540 = 1120 := by decide

@[simp] private theorem pc541 :
    Artifact.referenceArtifact.instructionPC 541 = 1121 := by decide

@[simp] private theorem pc542 :
    Artifact.referenceArtifact.instructionPC 542 = 1124 := by decide

@[simp] private theorem pc545 :
    Artifact.referenceArtifact.instructionPC 545 = 1128 := by decide

@[simp] private theorem pc546 :
    Artifact.referenceArtifact.instructionPC 546 = 1129 := by decide

@[simp] private theorem pc547 :
    Artifact.referenceArtifact.instructionPC 547 = 1130 := by decide

@[simp] private theorem pc548 :
    Artifact.referenceArtifact.instructionPC 548 = 1132 := by decide

@[simp] private theorem pc549 :
    Artifact.referenceArtifact.instructionPC 549 = 1133 := by decide

@[simp] private theorem pc550 :
    Artifact.referenceArtifact.instructionPC 550 = 1136 := by decide

@[simp] private theorem pc551 :
    Artifact.referenceArtifact.instructionPC 551 = 1137 := by decide

@[simp] private theorem pc552 :
    Artifact.referenceArtifact.instructionPC 552 = 1138 := by decide

@[simp] private theorem pc553 :
    Artifact.referenceArtifact.instructionPC 553 = 1140 := by decide

@[simp] private theorem pc554 :
    Artifact.referenceArtifact.instructionPC 554 = 1141 := by decide

@[simp] private theorem pc555 :
    Artifact.referenceArtifact.instructionPC 555 = 1142 := by decide

@[simp] private theorem pc556 :
    Artifact.referenceArtifact.instructionPC 556 = 1144 := by decide

@[simp] private theorem pc557 :
    Artifact.referenceArtifact.instructionPC 557 = 1145 := by decide

@[simp] private theorem pc558 :
    Artifact.referenceArtifact.instructionPC 558 = 1148 := by decide

@[simp] private theorem pc559 :
    Artifact.referenceArtifact.instructionPC 559 = 1149 := by decide

@[simp] private theorem pc591 :
    Artifact.referenceArtifact.instructionPC 591 = 1194 := by decide

@[simp] private theorem pc592 :
    Artifact.referenceArtifact.instructionPC 592 = 1195 := by decide

@[simp] private theorem pc593 :
    Artifact.referenceArtifact.instructionPC 593 = 1197 := by decide

@[simp] private theorem pc594 :
    Artifact.referenceArtifact.instructionPC 594 = 1198 := by decide

@[simp] private theorem pc595 :
    Artifact.referenceArtifact.instructionPC 595 = 1199 := by decide

@[simp] private theorem pc596 :
    Artifact.referenceArtifact.instructionPC 596 = 1201 := by decide

@[simp] private theorem pc597 :
    Artifact.referenceArtifact.instructionPC 597 = 1202 := by decide

@[simp] private theorem pc598 :
    Artifact.referenceArtifact.instructionPC 598 = 1205 := by decide

@[simp] private theorem pc599 :
    Artifact.referenceArtifact.instructionPC 599 = 1206 := by decide

@[simp] private theorem pc600 :
    Artifact.referenceArtifact.instructionPC 600 = 1207 := by decide

@[simp] private theorem pc601 :
    Artifact.referenceArtifact.instructionPC 601 = 1209 := by decide

@[simp] private theorem pc602 :
    Artifact.referenceArtifact.instructionPC 602 = 1210 := by decide

@[simp] private theorem pc603 :
    Artifact.referenceArtifact.instructionPC 603 = 1211 := by decide

@[simp] private theorem pc604 :
    Artifact.referenceArtifact.instructionPC 604 = 1213 := by decide

@[simp] private theorem pc605 :
    Artifact.referenceArtifact.instructionPC 605 = 1214 := by decide

@[simp] private theorem pc606 :
    Artifact.referenceArtifact.instructionPC 606 = 1217 := by decide

@[simp] private theorem pc607 :
    Artifact.referenceArtifact.instructionPC 607 = 1218 := by decide

@[simp] private theorem pc608 :
    Artifact.referenceArtifact.instructionPC 608 = 1219 := by decide

@[simp] private theorem pc609 :
    Artifact.referenceArtifact.instructionPC 609 = 1222 := by decide

@[simp] private theorem pc610 :
    Artifact.referenceArtifact.instructionPC 610 = 1223 := by decide

@[simp] private theorem pc611 :
    Artifact.referenceArtifact.instructionPC 611 = 1226 := by decide

@[simp] private theorem pc612 :
    Artifact.referenceArtifact.instructionPC 612 = 1227 := by decide

@[simp] private theorem pc613 :
    Artifact.referenceArtifact.instructionPC 613 = 1228 := by decide

@[simp] private theorem pc614 :
    Artifact.referenceArtifact.instructionPC 614 = 1229 := by decide

@[simp] private theorem pc615 :
    Artifact.referenceArtifact.instructionPC 615 = 1230 := by decide

@[simp] private theorem pc616 :
    Artifact.referenceArtifact.instructionPC 616 = 1231 := by decide

@[simp] private theorem pc617 :
    Artifact.referenceArtifact.instructionPC 617 = 1232 := by decide

@[simp] private theorem pc618 :
    Artifact.referenceArtifact.instructionPC 618 = 1237 := by decide

@[simp] private theorem pc619 :
    Artifact.referenceArtifact.instructionPC 619 = 1238 := by decide

@[simp] private theorem pc620 :
    Artifact.referenceArtifact.instructionPC 620 = 1241 := by decide

@[simp] private theorem pc621 :
    Artifact.referenceArtifact.instructionPC 621 = 1242 := by decide

@[simp] private theorem pc622 :
    Artifact.referenceArtifact.instructionPC 622 = 1243 := by decide

@[simp] private theorem pc623 :
    Artifact.referenceArtifact.instructionPC 623 = 1246 := by decide

@[simp] private theorem pc624 :
    Artifact.referenceArtifact.instructionPC 624 = 1247 := by decide

@[simp] private theorem pc625 :
    Artifact.referenceArtifact.instructionPC 625 = 1248 := by decide

@[simp] private theorem pc626 :
    Artifact.referenceArtifact.instructionPC 626 = 1249 := by decide

@[simp] private theorem pc627 :
    Artifact.referenceArtifact.instructionPC 627 = 1251 := by decide

@[simp] private theorem pc628 :
    Artifact.referenceArtifact.instructionPC 628 = 1252 := by decide

@[simp] private theorem pc629 :
    Artifact.referenceArtifact.instructionPC 629 = 1255 := by decide

@[simp] private theorem toNat1096 : (UInt256.ofNat 1096).toNat = 1096 := by decide
@[simp] private theorem toNat1098 : (UInt256.ofNat 1098).toNat = 1098 := by decide
@[simp] private theorem toNat1099 : (UInt256.ofNat 1099).toNat = 1099 := by decide
@[simp] private theorem toNat1100 : (UInt256.ofNat 1100).toNat = 1100 := by decide
@[simp] private theorem toNat1103 : (UInt256.ofNat 1103).toNat = 1103 := by decide
@[simp] private theorem toNat1104 : (UInt256.ofNat 1104).toNat = 1104 := by decide
@[simp] private theorem toNat1105 : (UInt256.ofNat 1105).toNat = 1105 := by decide
@[simp] private theorem toNat1108 : (UInt256.ofNat 1108).toNat = 1108 := by decide
@[simp] private theorem toNat1111 : (UInt256.ofNat 1111).toNat = 1111 := by decide
@[simp] private theorem toNat1114 : (UInt256.ofNat 1114).toNat = 1114 := by decide
@[simp] private theorem toNat1115 : (UInt256.ofNat 1115).toNat = 1115 := by decide
@[simp] private theorem toNat1116 : (UInt256.ofNat 1116).toNat = 1116 := by decide
@[simp] private theorem toNat1119 : (UInt256.ofNat 1119).toNat = 1119 := by decide
@[simp] private theorem toNat1120 : (UInt256.ofNat 1120).toNat = 1120 := by decide
@[simp] private theorem toNat1121 : (UInt256.ofNat 1121).toNat = 1121 := by decide
@[simp] private theorem toNat1124 : (UInt256.ofNat 1124).toNat = 1124 := by decide
@[simp] private theorem toNat1128 : (UInt256.ofNat 1128).toNat = 1128 := by decide
@[simp] private theorem toNat1129 : (UInt256.ofNat 1129).toNat = 1129 := by decide
@[simp] private theorem toNat1130 : (UInt256.ofNat 1130).toNat = 1130 := by decide
@[simp] private theorem toNat1132 : (UInt256.ofNat 1132).toNat = 1132 := by decide
@[simp] private theorem toNat1133 : (UInt256.ofNat 1133).toNat = 1133 := by decide
@[simp] private theorem toNat1136 : (UInt256.ofNat 1136).toNat = 1136 := by decide
@[simp] private theorem toNat1137 : (UInt256.ofNat 1137).toNat = 1137 := by decide
@[simp] private theorem toNat1138 : (UInt256.ofNat 1138).toNat = 1138 := by decide
@[simp] private theorem toNat1140 : (UInt256.ofNat 1140).toNat = 1140 := by decide
@[simp] private theorem toNat1141 : (UInt256.ofNat 1141).toNat = 1141 := by decide
@[simp] private theorem toNat1142 : (UInt256.ofNat 1142).toNat = 1142 := by decide
@[simp] private theorem toNat1144 : (UInt256.ofNat 1144).toNat = 1144 := by decide
@[simp] private theorem toNat1145 : (UInt256.ofNat 1145).toNat = 1145 := by decide
@[simp] private theorem toNat1148 : (UInt256.ofNat 1148).toNat = 1148 := by decide
@[simp] private theorem toNat1149 : (UInt256.ofNat 1149).toNat = 1149 := by decide
@[simp] private theorem toNat1194 : (UInt256.ofNat 1194).toNat = 1194 := by decide
@[simp] private theorem toNat1195 : (UInt256.ofNat 1195).toNat = 1195 := by decide
@[simp] private theorem toNat1197 : (UInt256.ofNat 1197).toNat = 1197 := by decide
@[simp] private theorem toNat1198 : (UInt256.ofNat 1198).toNat = 1198 := by decide
@[simp] private theorem toNat1199 : (UInt256.ofNat 1199).toNat = 1199 := by decide
@[simp] private theorem toNat1201 : (UInt256.ofNat 1201).toNat = 1201 := by decide
@[simp] private theorem toNat1202 : (UInt256.ofNat 1202).toNat = 1202 := by decide
@[simp] private theorem toNat1205 : (UInt256.ofNat 1205).toNat = 1205 := by decide
@[simp] private theorem toNat1206 : (UInt256.ofNat 1206).toNat = 1206 := by decide
@[simp] private theorem toNat1207 : (UInt256.ofNat 1207).toNat = 1207 := by decide
@[simp] private theorem toNat1209 : (UInt256.ofNat 1209).toNat = 1209 := by decide
@[simp] private theorem toNat1210 : (UInt256.ofNat 1210).toNat = 1210 := by decide
@[simp] private theorem toNat1211 : (UInt256.ofNat 1211).toNat = 1211 := by decide
@[simp] private theorem toNat1213 : (UInt256.ofNat 1213).toNat = 1213 := by decide
@[simp] private theorem toNat1214 : (UInt256.ofNat 1214).toNat = 1214 := by decide
@[simp] private theorem toNat1217 : (UInt256.ofNat 1217).toNat = 1217 := by decide
@[simp] private theorem toNat1218 : (UInt256.ofNat 1218).toNat = 1218 := by decide
@[simp] private theorem toNat1219 : (UInt256.ofNat 1219).toNat = 1219 := by decide
@[simp] private theorem toNat1222 : (UInt256.ofNat 1222).toNat = 1222 := by decide
@[simp] private theorem toNat1223 : (UInt256.ofNat 1223).toNat = 1223 := by decide
@[simp] private theorem toNat1226 : (UInt256.ofNat 1226).toNat = 1226 := by decide
@[simp] private theorem toNat1227 : (UInt256.ofNat 1227).toNat = 1227 := by decide
@[simp] private theorem toNat1228 : (UInt256.ofNat 1228).toNat = 1228 := by decide
@[simp] private theorem toNat1229 : (UInt256.ofNat 1229).toNat = 1229 := by decide
@[simp] private theorem toNat1230 : (UInt256.ofNat 1230).toNat = 1230 := by decide
@[simp] private theorem toNat1231 : (UInt256.ofNat 1231).toNat = 1231 := by decide
@[simp] private theorem toNat1232 : (UInt256.ofNat 1232).toNat = 1232 := by decide
@[simp] private theorem toNat1237 : (UInt256.ofNat 1237).toNat = 1237 := by decide
@[simp] private theorem toNat1238 : (UInt256.ofNat 1238).toNat = 1238 := by decide
@[simp] private theorem toNat1241 : (UInt256.ofNat 1241).toNat = 1241 := by decide
@[simp] private theorem toNat1242 : (UInt256.ofNat 1242).toNat = 1242 := by decide
@[simp] private theorem toNat1243 : (UInt256.ofNat 1243).toNat = 1243 := by decide
@[simp] private theorem toNat1246 : (UInt256.ofNat 1246).toNat = 1246 := by decide
@[simp] private theorem toNat1247 : (UInt256.ofNat 1247).toNat = 1247 := by decide
@[simp] private theorem toNat1248 : (UInt256.ofNat 1248).toNat = 1248 := by decide
@[simp] private theorem toNat1249 : (UInt256.ofNat 1249).toNat = 1249 := by decide
@[simp] private theorem toNat1251 : (UInt256.ofNat 1251).toNat = 1251 := by decide
@[simp] private theorem toNat1252 : (UInt256.ofNat 1252).toNat = 1252 := by decide
@[simp] private theorem toNat1255 : (UInt256.ofNat 1255).toNat = 1255 := by decide

@[simp] private theorem next526 : (UInt256.ofNat 1095).succ = UInt256.ofNat 1096 := by decide
@[simp] private theorem next527 : UInt256.ofNat 1096 + UInt256.ofNat 2 = UInt256.ofNat 1098 := by decide
@[simp] private theorem next528 : (UInt256.ofNat 1098).succ = UInt256.ofNat 1099 := by decide
@[simp] private theorem next529 : (UInt256.ofNat 1099).succ = UInt256.ofNat 1100 := by decide
@[simp] private theorem next530 : UInt256.ofNat 1100 + UInt256.ofNat 3 = UInt256.ofNat 1103 := by decide
@[simp] private theorem next531 : (UInt256.ofNat 1103).succ = UInt256.ofNat 1104 := by decide
@[simp] private theorem next532 : (UInt256.ofNat 1104).succ = UInt256.ofNat 1105 := by decide
@[simp] private theorem next533 : UInt256.ofNat 1105 + UInt256.ofNat 3 = UInt256.ofNat 1108 := by decide
@[simp] private theorem next534 : UInt256.ofNat 1108 + UInt256.ofNat 3 = UInt256.ofNat 1111 := by decide
@[simp] private theorem next535 : UInt256.ofNat 1111 + UInt256.ofNat 3 = UInt256.ofNat 1114 := by decide
@[simp] private theorem next536 : (UInt256.ofNat 1114).succ = UInt256.ofNat 1115 := by decide
@[simp] private theorem next537 : (UInt256.ofNat 1115).succ = UInt256.ofNat 1116 := by decide
@[simp] private theorem next538 : UInt256.ofNat 1116 + UInt256.ofNat 3 = UInt256.ofNat 1119 := by decide
@[simp] private theorem next539 : (UInt256.ofNat 1119).succ = UInt256.ofNat 1120 := by decide
@[simp] private theorem next540 : (UInt256.ofNat 1120).succ = UInt256.ofNat 1121 := by decide
@[simp] private theorem next541 : UInt256.ofNat 1121 + UInt256.ofNat 3 = UInt256.ofNat 1124 := by decide
@[simp] private theorem next542 : (UInt256.ofNat 1124).succ = UInt256.ofNat 1125 := by decide
@[simp] private theorem next544 : UInt256.ofNat 1126 + UInt256.ofNat 2 = UInt256.ofNat 1128 := by decide
@[simp] private theorem next545 : (UInt256.ofNat 1128).succ = UInt256.ofNat 1129 := by decide
@[simp] private theorem next546 : (UInt256.ofNat 1129).succ = UInt256.ofNat 1130 := by decide
@[simp] private theorem next547 : UInt256.ofNat 1130 + UInt256.ofNat 2 = UInt256.ofNat 1132 := by decide
@[simp] private theorem next548 : (UInt256.ofNat 1132).succ = UInt256.ofNat 1133 := by decide
@[simp] private theorem next549 : UInt256.ofNat 1133 + UInt256.ofNat 3 = UInt256.ofNat 1136 := by decide
@[simp] private theorem next550 : (UInt256.ofNat 1136).succ = UInt256.ofNat 1137 := by decide
@[simp] private theorem next551 : (UInt256.ofNat 1137).succ = UInt256.ofNat 1138 := by decide
@[simp] private theorem next552 : UInt256.ofNat 1138 + UInt256.ofNat 2 = UInt256.ofNat 1140 := by decide
@[simp] private theorem next553 : (UInt256.ofNat 1140).succ = UInt256.ofNat 1141 := by decide
@[simp] private theorem next554 : (UInt256.ofNat 1141).succ = UInt256.ofNat 1142 := by decide
@[simp] private theorem next555 : UInt256.ofNat 1142 + UInt256.ofNat 2 = UInt256.ofNat 1144 := by decide
@[simp] private theorem next556 : (UInt256.ofNat 1144).succ = UInt256.ofNat 1145 := by decide
@[simp] private theorem next557 : UInt256.ofNat 1145 + UInt256.ofNat 3 = UInt256.ofNat 1148 := by decide
@[simp] private theorem next558 : (UInt256.ofNat 1148).succ = UInt256.ofNat 1149 := by decide
@[simp] private theorem next559 : (UInt256.ofNat 1149).succ = UInt256.ofNat 1150 := by decide
@[simp] private theorem next591 : (UInt256.ofNat 1194).succ = UInt256.ofNat 1195 := by decide
@[simp] private theorem next592 : UInt256.ofNat 1195 + UInt256.ofNat 2 = UInt256.ofNat 1197 := by decide
@[simp] private theorem next593 : (UInt256.ofNat 1197).succ = UInt256.ofNat 1198 := by decide
@[simp] private theorem next594 : (UInt256.ofNat 1198).succ = UInt256.ofNat 1199 := by decide
@[simp] private theorem next595 : UInt256.ofNat 1199 + UInt256.ofNat 2 = UInt256.ofNat 1201 := by decide
@[simp] private theorem next596 : (UInt256.ofNat 1201).succ = UInt256.ofNat 1202 := by decide
@[simp] private theorem next597 : UInt256.ofNat 1202 + UInt256.ofNat 3 = UInt256.ofNat 1205 := by decide
@[simp] private theorem next598 : (UInt256.ofNat 1205).succ = UInt256.ofNat 1206 := by decide
@[simp] private theorem next599 : (UInt256.ofNat 1206).succ = UInt256.ofNat 1207 := by decide
@[simp] private theorem next600 : UInt256.ofNat 1207 + UInt256.ofNat 2 = UInt256.ofNat 1209 := by decide
@[simp] private theorem next601 : (UInt256.ofNat 1209).succ = UInt256.ofNat 1210 := by decide
@[simp] private theorem next602 : (UInt256.ofNat 1210).succ = UInt256.ofNat 1211 := by decide
@[simp] private theorem next603 : UInt256.ofNat 1211 + UInt256.ofNat 2 = UInt256.ofNat 1213 := by decide
@[simp] private theorem next604 : (UInt256.ofNat 1213).succ = UInt256.ofNat 1214 := by decide
@[simp] private theorem next605 : UInt256.ofNat 1214 + UInt256.ofNat 3 = UInt256.ofNat 1217 := by decide
@[simp] private theorem next606 : (UInt256.ofNat 1217).succ = UInt256.ofNat 1218 := by decide
@[simp] private theorem next607 : (UInt256.ofNat 1218).succ = UInt256.ofNat 1219 := by decide
@[simp] private theorem next608 : UInt256.ofNat 1219 + UInt256.ofNat 3 = UInt256.ofNat 1222 := by decide
@[simp] private theorem next609 : (UInt256.ofNat 1222).succ = UInt256.ofNat 1223 := by decide
@[simp] private theorem next610 : UInt256.ofNat 1223 + UInt256.ofNat 3 = UInt256.ofNat 1226 := by decide
@[simp] private theorem next611 : (UInt256.ofNat 1226).succ = UInt256.ofNat 1227 := by decide
@[simp] private theorem next612 : (UInt256.ofNat 1227).succ = UInt256.ofNat 1228 := by decide
@[simp] private theorem next613 : (UInt256.ofNat 1228).succ = UInt256.ofNat 1229 := by decide
@[simp] private theorem next614 : (UInt256.ofNat 1229).succ = UInt256.ofNat 1230 := by decide
@[simp] private theorem next615 : (UInt256.ofNat 1230).succ = UInt256.ofNat 1231 := by decide
@[simp] private theorem next616 : (UInt256.ofNat 1231).succ = UInt256.ofNat 1232 := by decide
@[simp] private theorem next617 : UInt256.ofNat 1232 + UInt256.ofNat 5 = UInt256.ofNat 1237 := by decide
@[simp] private theorem next618 : (UInt256.ofNat 1237).succ = UInt256.ofNat 1238 := by decide
@[simp] private theorem next619 : UInt256.ofNat 1238 + UInt256.ofNat 3 = UInt256.ofNat 1241 := by decide
@[simp] private theorem next620 : (UInt256.ofNat 1241).succ = UInt256.ofNat 1242 := by decide
@[simp] private theorem next621 : (UInt256.ofNat 1242).succ = UInt256.ofNat 1243 := by decide
@[simp] private theorem next622 : UInt256.ofNat 1243 + UInt256.ofNat 3 = UInt256.ofNat 1246 := by decide
@[simp] private theorem next623 : (UInt256.ofNat 1246).succ = UInt256.ofNat 1247 := by decide
@[simp] private theorem next624 : (UInt256.ofNat 1247).succ = UInt256.ofNat 1248 := by decide
@[simp] private theorem next625 : (UInt256.ofNat 1248).succ = UInt256.ofNat 1249 := by decide
@[simp] private theorem next626 : UInt256.ofNat 1249 + UInt256.ofNat 2 = UInt256.ofNat 1251 := by decide
@[simp] private theorem next627 : (UInt256.ofNat 1251).succ = UInt256.ofNat 1252 := by decide
@[simp] private theorem next628 : UInt256.ofNat 1252 + UInt256.ofNat 3 = UInt256.ofNat 1255 := by decide

def extConditionPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨526, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨527, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨528, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨529, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨530, .push ⟨2, by decide⟩ (UInt256.ofNat 0x465), by rfl, by decide⟩,
   ⟨531, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Loads `W[k-16]` then `W[k-15]`, leaving the latter on top for sigma-0. -/
def extLoadsPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨543, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨544, .push ⟨1, by decide⟩ (UInt256.ofNat 16), by rfl, by decide⟩,
   ⟨545, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨546, .op .SUB, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨547, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨548, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨549, .push ⟨2, by decide⟩ (UInt256.ofNat 0x320), by rfl, by decide⟩,
   ⟨550, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨551, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨552, .push ⟨1, by decide⟩ (UInt256.ofNat 15), by rfl, by decide⟩,
   ⟨553, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨554, .op .SUB, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨555, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨556, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨557, .push ⟨2, by decide⟩ (UInt256.ofNat 0x320), by rfl, by decide⟩,
   ⟨558, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨559, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Adds `W[k-16]`, loads `W[k-7]` and `W[k-2]`, and sets up the `smallSigma1`
call. -/
def extMiddlePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨591, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨592, .push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨593, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨594, .op .SUB, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨595, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨596, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨597, .push ⟨2, by decide⟩ (UInt256.ofNat 0x320), by rfl, by decide⟩,
   ⟨598, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨599, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨600, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨601, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨602, .op .SUB, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨603, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨604, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨605, .push ⟨2, by decide⟩ (UInt256.ofNat 0x320), by rfl, by decide⟩,
   ⟨606, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨607, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨608, .push ⟨2, by decide⟩ (UInt256.ofNat 0x4cb), by rfl, by decide⟩,
   ⟨609, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨610, .push ⟨2, by decide⟩ (UInt256.ofNat 0x5dd), by rfl, by decide⟩,
   ⟨611, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Folds sigma-1's result in, masks to 32 bits, and sets up the `wSet` call. -/
def extCombinePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨612, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨613, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨614, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨615, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨616, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨617, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨618, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨619, .push ⟨2, by decide⟩ (UInt256.ofNat 0x4df), by rfl, by decide⟩,
   ⟨620, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨621, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨622, .push ⟨2, by decide⟩ (UInt256.ofNat 0x683), by rfl, by decide⟩,
   ⟨623, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Drops the stored word and advances the counter. -/
def extAdvancePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨624, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨625, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨626, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨627, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨628, .push ⟨2, by decide⟩ (UInt256.ofNat 0x447), by rfl, by decide⟩,
   ⟨629, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

/-- The exit: the condition falling through at `k = 64`, then the `MCOPY` of the
chaining values into the working area and the jump to the compression loop. -/
def extExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨526, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨527, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨528, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨529, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨530, .push ⟨2, by decide⟩ (UInt256.ofNat 0x465), by rfl, by decide⟩,
   ⟨531, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨532, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨533, .push ⟨2, by decide⟩ (UInt256.ofNat 0x100), by rfl, by decide⟩,
   ⟨534, .push ⟨2, by decide⟩ (UInt256.ofNat 0x120), by rfl, by decide⟩,
   ⟨535, .push ⟨2, by decide⟩ (UInt256.ofNat 0x220), by rfl, by decide⟩,
   ⟨536, .op .MCOPY, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨537, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨538, .push ⟨2, by decide⟩ (UInt256.ofNat 0x23f), by rfl, by decide⟩,
   ⟨539, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

/-! ### Extension-loop state model

The four reads are at `W[k-16]`, `W[k-15]`, `W[k-7]` and `W[k-2]`, and the write
is at `W[k]`.  As in the first loop each read is taken from memory as it stands
when the iteration runs — which here is not merely equivalent to reading the
original but *required*: `W[k-2]` is a word this loop wrote two iterations ago. -/

/-- `W[k - off]`, read from `memory`. -/
def wRead (memory : ByteArray) (k : UInt256) (off : Nat) : UInt256 :=
  MachineState.readWord memory (wSlotAddr (k - UInt256.ofNat off)).toNat

/-- The word iteration `k` stores: the four terms summed and truncated to 32
bits, in the association and operand order the bytecode uses. -/
def extWord (memory : ByteArray) (k : UInt256) : UInt256 :=
  UInt256.land (UInt256.ofNat 4294967295)
    ((Functions.smallSigma1Word (wRead memory k 2) + wRead memory k 7) +
      (Functions.smallSigma0Word (wRead memory k 15) + wRead memory k 16))

/-- Memory after the extension loop has written `n` words, starting at `W[16]`. -/
def extMemory (base : ByteArray) : Nat → ByteArray
  | 0 => base
  | n + 1 =>
      let prev := extMemory base n
      MachineState.writeBytes prev
        (Data.Bytes.natToBytesPadded
          (extWord prev (UInt256.ofNat (16 + n))).toNat 32)
        (wSlotAddr (UInt256.ofNat (16 + n))).toNat

/-- Active words after `n` extension iterations.  Each iteration touches memory
five times: the four reads, then the write. -/
def extActiveWords (base : UInt256) (mem : ByteArray) : Nat → UInt256
  | 0 => base
  | n + 1 =>
      let k := UInt256.ofNat (16 + n)
      let step (aw : UInt256) (addr : UInt256) : UInt256 :=
        UInt256.ofNat (MachineState.activeWordsAfter aw.toNat addr.toNat 32)
      let aw := extActiveWords base mem n
      step (step (step (step (step aw (wSlotAddr (k - UInt256.ofNat 16)))
        (wSlotAddr (k - UInt256.ofNat 15)))
        (wSlotAddr (k - UInt256.ofNat 7)))
        (wSlotAddr (k - UInt256.ofNat 2)))
        (wSlotAddr k)

/-- The extension loop's state at counter `16 + n`. -/
def extLoopState (s : State) (rest : List UInt256) (n : Nat) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 526)
    stack := UInt256.ofNat (16 + n) :: rest
    memory := extMemory s.memory n
    activeWords := extActiveWords s.activeWords s.memory n }

end Challenge.Sha256.Reference.Proofs.Bytecode.Schedule
