import Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact
import Challenge.EvmProof.Meter

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-!
# Direct bytecode trace for the RIPEMD-160 message schedule

The reference schedule has one sixteen-iteration loop.  Each iteration calls
the compiled `readLE32` and `xSet` helpers, loading four message bytes and
storing the resulting 32-bit word in the dedicated `X[i]` slot.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.Schedule

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

@[simp] private theorem succSmall (n : Nat) (h : n + 1 < 2 ^ 256) :
    (UInt256.ofNat n).succ = UInt256.ofNat (n + 1) :=
  Challenge.EvmProof.Word.succ_ofNat h

@[simp] private theorem addSmall (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.EvmProof.Word.ofNat_add_ofNat h

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka

def scheduleStartPath : List Located :=
  [⟨413, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨414, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩]

def conditionPath : List Located :=
  [⟨415, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨416, .push ⟨1, by decide⟩ (UInt256.ofNat 16), by rfl, by decide⟩,
   ⟨417, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨418, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨419, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨420, .push ⟨2, by decide⟩ (UInt256.ofNat 0x264), by rfl, by decide⟩,
   ⟨421, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def setupReadPath : List Located :=
  [⟨422, .push ⟨2, by decide⟩ (UInt256.ofNat 0x259), by rfl, by decide⟩,
   ⟨423, .push ⟨2, by decide⟩ (UInt256.ofNat 0x253), by rfl, by decide⟩,
   ⟨424, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨425, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨426, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨427, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨428, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨429, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨430, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1b7), by rfl, by decide⟩,
   ⟨431, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def readLEPath : List Located :=
  [⟨316, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨317, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨318, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨319, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨320, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨321, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨322, .push ⟨1, by decide⟩ (UInt256.ofNat 24), by rfl, by decide⟩,
   ⟨323, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨324, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨325, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨326, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨327, .push ⟨1, by decide⟩ (UInt256.ofNat 16), by rfl, by decide⟩,
   ⟨328, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨329, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨330, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨331, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨332, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨333, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨334, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨335, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨336, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨337, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨338, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨339, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨340, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨341, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨342, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨343, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨344, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨345, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Maximal prefix executable by the current generic stepper.  The next
instruction is `BYTE`, which is the one missing `runInstr` case. -/
def readLEPrefixPath : List Located := readLEPath.take 5

def setupXSetPath : List Located :=
  [⟨432, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨433, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨434, .push ⟨2, by decide⟩ (UInt256.ofNat 0x5f), by rfl, by decide⟩,
   ⟨435, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def xSetPath : List Located :=
  [⟨70, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨71, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨72, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨73, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨74, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨75, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨76, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨77, .push ⟨2, by decide⟩ (UInt256.ofNat 0x2a0), by rfl, by decide⟩,
   ⟨78, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨79, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨80, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨81, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨82, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def incrementPath : List Located :=
  [⟨436, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨437, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨438, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨439, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨440, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨441, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨442, .push ⟨2, by decide⟩ (UInt256.ofNat 0x238), by rfl, by decide⟩,
   ⟨443, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def exitPath : List Located :=
  [⟨444, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨445, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨446, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨447, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem schedulePC (i : Nat) (hlo : 413 ≤ i) (hhi : i ≤ 447) :
    Artifact.referenceArtifact.instructionPC i =
      [0x236, 0x237, 0x238, 0x239, 0x23b, 0x23c, 0x23d, 0x23e,
       0x241, 0x242, 0x245, 0x248, 0x249, 0x24a, 0x24c, 0x24d,
       0x24e, 0x24f, 0x252, 0x253, 0x254, 0x255, 0x258, 0x259,
       0x25a, 0x25c, 0x25d, 0x25e, 0x25f, 0x260, 0x263, 0x264,
       0x265, 0x266, 0x267][i - 413]! := by
  interval_cases i <;> rfl

@[simp] private theorem readPC (i : Nat) (hlo : 316 ≤ i) (hhi : i ≤ 345) :
    Artifact.referenceArtifact.instructionPC i =
      [0x1b7, 0x1b8, 0x1b9, 0x1ba, 0x1bb, 0x1bd, 0x1be, 0x1c0,
       0x1c1, 0x1c2, 0x1c4, 0x1c5, 0x1c7, 0x1c8, 0x1c9, 0x1ca,
       0x1cc, 0x1cd, 0x1cf, 0x1d0, 0x1d1, 0x1d2, 0x1d3, 0x1d4,
       0x1d5, 0x1d6, 0x1d7, 0x1d8, 0x1d9, 0x1da][i - 316]! := by
  interval_cases i <;> rfl

@[simp] private theorem xSetPC (i : Nat) (hlo : 70 ≤ i) (hhi : i ≤ 82) :
    Artifact.referenceArtifact.instructionPC i =
      [0x5f, 0x60, 0x65, 0x66, 0x67, 0x68, 0x6a,
       0x6b, 0x6e, 0x6f, 0x70, 0x71, 0x72][i - 70]! := by
  interval_cases i <;> rfl

def loadOffsetWord (msgOff : UInt256) (i : Nat) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 2) + msgOff

def xSlotWord (i : Nat) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) + UInt256.ofNat 0x2a0

def readLEWord (memory : ByteArray) (off : UInt256) : UInt256 :=
  let w := MachineState.readWord memory off.toNat
  UInt256.lor
    (UInt256.lor (UInt256.byteAt ⟨0⟩ w)
      (UInt256.shiftLeft (UInt256.byteAt (UInt256.ofNat 1) w)
        (UInt256.ofNat 8)))
    (UInt256.lor
      (UInt256.shiftLeft (UInt256.byteAt (UInt256.ofNat 2) w)
        (UInt256.ofNat 16))
      (UInt256.shiftLeft (UInt256.byteAt (UInt256.ofNat 3) w)
        (UInt256.ofNat 24)))

def scheduleEntry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x236
           stack := [msgOff, returnDest] ++ rest }

def loopAt (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 0x238
           stack := [UInt256.ofNat i, msgOff, returnDest] ++ rest }

def afterCondition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 0x242
           stack := [UInt256.ofNat i, msgOff, returnDest] ++ rest }

def readEntry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 0x1b7
           stack := [loadOffsetWord msgOff i, 0, UInt256.ofNat 0x253,
             UInt256.ofNat 0x259, UInt256.ofNat i, msgOff, returnDest] ++ rest }

def afterRead (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 0x253
           stack := [readLEWord s.memory (loadOffsetWord msgOff i),
             UInt256.ofNat 0x259, UInt256.ofNat i, msgOff, returnDest] ++ rest
           activeWords := s.activeWordsAfterUInt256
             (loadOffsetWord msgOff i).toNat 32 }

def beforeFirstByte (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  let off := loadOffsetWord msgOff i
  let w := MachineState.readWord s.memory off.toNat
  { s with
    pc := UInt256.ofNat 0x1bd
    stack := [UInt256.ofNat 3, w, w, off, 0, UInt256.ofNat 0x253,
      UInt256.ofNat 0x259, UInt256.ofNat i, msgOff, returnDest] ++ rest
    activeWords := s.activeWordsAfterUInt256 off.toNat 32 }

def xSetEntry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  let loaded := afterRead s msgOff returnDest rest i
  { loaded with
    pc := UInt256.ofNat 0x5f
    stack := [UInt256.ofNat i,
        readLEWord s.memory (loadOffsetWord msgOff i), UInt256.ofNat 0x259,
        UInt256.ofNat i, msgOff, returnDest] ++ rest }

def afterStore (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  let loaded := afterRead s msgOff returnDest rest i
  let value := UInt256.land (readLEWord s.memory (loadOffsetWord msgOff i))
    (UInt256.ofNat 0xffffffff)
  { loaded with
    pc := UInt256.ofNat 0x259
    stack := [UInt256.ofNat i, msgOff, returnDest] ++ rest
    memory := MachineState.writeBytes loaded.memory
      (Data.Bytes.natToBytesPadded value.toNat 32) (xSlotWord i).toNat
    activeWords := loaded.activeWordsAfterUInt256 (xSlotWord i).toNat 32 }

def afterIteration (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { afterStore s msgOff returnDest rest i with
      pc := UInt256.ofNat 0x238
      stack := [UInt256.ofNat (i + 1), msgOff, returnDest] ++ rest }

set_option linter.unusedSimpArgs false in
theorem run_scheduleStart (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock scheduleStartPath
      (scheduleEntry s msgOff returnDest rest) =
        some (loopAt s msgOff returnDest rest 0) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  simp [scheduleStartPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    scheduleEntry, loopAt, hc2, hrun]
  decide

set_option linter.unusedSimpArgs false in
theorem run_condition_continue (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 16)
    (hstack : rest.length < 1019) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock conditionPath
      (loopAt s msgOff returnDest rest i) =
        some (afterCondition s msgOff returnDest rest i) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hiWord : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat 16) =
      UInt256.ofNat 1 := by
    simp [UInt256.lt, hiWord, Challenge.EvmProof.Word.word_toNat_ofNat, hi]
  have hzero : UInt256.isZero (UInt256.ofNat 1) = 0 := by decide
  have hfalse : UInt256.isTrue (0 : UInt256) = false := by decide
  simp [conditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopAt, afterCondition, hc3, hc4, hc5, hrun, hlt, hzero, hfalse]

set_option linter.unusedSimpArgs false in
theorem run_setupRead (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (_hi : i < 16)
    (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupReadPath
      (afterCondition s msgOff returnDest rest i) =
        some (readEntry s msgOff returnDest rest i) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 0x1b7 = true := by decide
  have hoff : msgOff + UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 2) =
      loadOffsetWord msgOff i := by
    rw [loadOffsetWord]
    exact Challenge.EvmProof.Word.word_add_comm _ _
  simp [setupReadPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterCondition, readEntry, hc3, hc4, hc5, hc6, hc7, hc8, hrun, hcode,
    hdest, hoff]
  decide

set_option linter.unusedSimpArgs false in
theorem run_readLEPrefix (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hstack : rest.length < 1014)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock readLEPrefixPath
      (readEntry s msgOff returnDest rest i) =
        some (beforeFirstByte s msgOff returnDest rest i) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  simp [readLEPrefixPath, readLEPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    readEntry, beforeFirstByte,
    hc7, hc8, hc9, hc10, hrun,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_readLE (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock readLEPath
      (readEntry s msgOff returnDest rest i) =
        some (afterRead s msgOff returnDest rest i) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 0x253 = true := by decide
  simp [readLEPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    readEntry, afterRead, readLEWord, List.exchange,
    hc6, hc7, hc8, hc9, hc10, hc11, hc12, hrun, hcode, hdest,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_setupXSet (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hstack : rest.length < 1017)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupXSetPath
      (afterRead s msgOff returnDest rest i) =
        some (xSetEntry s msgOff returnDest rest i) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 0x5f = true := by decide
  simp [setupXSetPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterRead, xSetEntry, hc5, hc6, hc7, hrun, hcode, hdest]

set_option linter.unusedSimpArgs false in
theorem run_xSet (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (_hi : i < 16)
    (hstack : rest.length < 1015)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock xSetPath
      (xSetEntry s msgOff returnDest rest i) =
        some (afterStore s msgOff returnDest rest i) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 0x259 = true := by decide
  have hslot : UInt256.ofNat 0x2a0 +
        UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) = xSlotWord i := by
    rw [xSlotWord]
    exact Challenge.EvmProof.Word.word_add_comm _ _
  simp [xSetPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    xSetEntry, afterStore, afterRead, List.exchange,
    hc4, hc5, hc6, hc7, hc8, hc9, hrun, hcode, hdest, hslot,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_increment (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 16)
    (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock incrementPath
      (afterStore s msgOff returnDest rest i) =
        some (afterIteration s msgOff returnDest rest i) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hadd : UInt256.ofNat i + UInt256.ofNat 1 = UInt256.ofNat (i + 1) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hdest : Decode.isValidJumpDest referenceBytecode 0x238 = true := by decide
  simp [incrementPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterStore, afterIteration, afterRead, List.exchange,
    hc3, hc4, hc5, hrun, hcode, hdest, hadd]

def gasSteps_readLEPrefix (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hstack : rest.length < 1014)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (readEntry s msgOff returnDest rest i)
      (beforeFirstByte s msgOff returnDest rest i) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka readLEPrefixPath
  · exact hcode
  · exact hfork
  · exact run_readLEPrefix s msgOff returnDest rest i hstack hrun
  · exact hrun
  · exact hnp

def gasSteps_readLE (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (readEntry s msgOff returnDest rest i)
      (afterRead s msgOff returnDest rest i) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka readLEPath
  · exact hcode
  · exact hfork
  · exact run_readLE s msgOff returnDest rest i hstack hcode hrun
  · exact hrun
  · exact hnp

/-- One complete schedule iteration, conditional only on the `readLE32`
helper trace whose four `BYTE` instructions are not yet supported by the
generic executable stepper. -/
def gasSteps_iteration_of_readLE (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 16)
    (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (gread : Challenge.EvmProof.GasSteps
      (readEntry s msgOff returnDest rest i)
      (afterRead s msgOff returnDest rest i)) :
    Challenge.EvmProof.GasSteps (loopAt s msgOff returnDest rest i)
      (afterIteration s msgOff returnDest rest i) := by
  have gCondition : Challenge.EvmProof.GasSteps
      (loopAt s msgOff returnDest rest i)
      (afterCondition s msgOff returnDest rest i) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka conditionPath
    · exact hcode
    · exact hfork
    · exact run_condition_continue s msgOff returnDest rest i hi (by omega) hrun
    · exact hrun
    · exact hnp
  have gSetupRead : Challenge.EvmProof.GasSteps
      (afterCondition s msgOff returnDest rest i)
      (readEntry s msgOff returnDest rest i) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupReadPath
    · exact hcode
    · exact hfork
    · exact run_setupRead s msgOff returnDest rest i hi (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have gSetupXSet : Challenge.EvmProof.GasSteps
      (afterRead s msgOff returnDest rest i)
      (xSetEntry s msgOff returnDest rest i) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupXSetPath
    · exact hcode
    · exact hfork
    · exact run_setupXSet s msgOff returnDest rest i (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have gXSet : Challenge.EvmProof.GasSteps
      (xSetEntry s msgOff returnDest rest i)
      (afterStore s msgOff returnDest rest i) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka xSetPath
    · exact hcode
    · exact hfork
    · exact run_xSet s msgOff returnDest rest i hi (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have gIncrement : Challenge.EvmProof.GasSteps
      (afterStore s msgOff returnDest rest i)
      (afterIteration s msgOff returnDest rest i) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka incrementPath
    · exact hcode
    · exact hfork
    · exact run_increment s msgOff returnDest rest i hi (by omega) hcode hrun
    · exact hrun
    · exact hnp
  exact gCondition.trans <| gSetupRead.trans <| gread.trans <|
    gSetupXSet.trans <| gXSet.trans gIncrement

def loopState (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : Nat → State
  | 0 => loopAt s msgOff returnDest rest 0
  | i + 1 => afterIteration (loopState s msgOff returnDest rest i)
      msgOff returnDest rest i

@[simp] theorem loopState_executionEnv (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (loopState s msgOff returnDest rest i).executionEnv = s.executionEnv := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [loopState, afterIteration, afterStore, afterRead, ih]

@[simp] theorem loopState_halt (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (loopState s msgOff returnDest rest i).halt = s.halt := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [loopState, afterIteration, afterStore, afterRead, ih]

@[simp] theorem loopAt_loopState (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    loopAt (loopState s msgOff returnDest rest i) msgOff returnDest rest i =
      loopState s msgOff returnDest rest i := by
  cases i <;> rfl

def gasSteps_loop_of_readLE (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hread : ∀ (i : Nat), i < 16 →
      Challenge.EvmProof.GasSteps
        (readEntry (loopState s msgOff returnDest rest i)
          msgOff returnDest rest i)
        (afterRead (loopState s msgOff returnDest rest i)
          msgOff returnDest rest i)) :
    Challenge.EvmProof.GasSteps (loopState s msgOff returnDest rest 0)
      (loopState s msgOff returnDest rest 16) := by
  apply Challenge.EvmProof.GasSteps.iterateBounded (count := 16)
  intro i hi
  let q := loopState s msgOff returnDest rest i
  have hqcode : q.executionEnv.code = referenceBytecode := by
    simpa [q] using hcode
  have hqfork : q.fork = .Osaka := by
    simpa [q, State.fork] using hfork
  have hqrun : q.halt = .Running := by simpa [q] using hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  let gone := gasSteps_iteration_of_readLE q msgOff returnDest rest i hi hstack
    hqcode hqfork hqrun hqnp (by simpa [q] using hread i hi)
  exact Challenge.EvmProof.GasSteps.cast gone (by simp [q]) (by
    simp [q, loopState])

def afterExitCondition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 0x264
    stack := [UInt256.ofNat 16, msgOff, returnDest] ++ rest }

def scheduleReturned (s : State) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := returnDest, stack := rest }

set_option linter.unusedSimpArgs false in
theorem run_condition_exit (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock conditionPath
      (loopAt s msgOff returnDest rest 16) =
        some (afterExitCondition s msgOff returnDest rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat 16) (UInt256.ofNat 16) = 0 := by decide
  have hzero : UInt256.isZero (0 : UInt256) = UInt256.ofNat 1 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) = true := by decide
  have hdest : Decode.isValidJumpDest referenceBytecode 0x264 = true := by decide
  simp [conditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopAt, afterExitCondition, hc3, hc4, hc5, hrun, hcode,
    hlt, hzero, htrue, hdest]

set_option linter.unusedSimpArgs false in
theorem run_exit (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock exitPath
      (afterExitCondition s msgOff returnDest rest) =
        some (scheduleReturned s returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  simp [exitPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterExitCondition, scheduleReturned, hc1, hc2, hc3, hrun, hcode, hreturn]

def gasSteps_scheduleStart (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (scheduleEntry s msgOff returnDest rest)
      (loopState s msgOff returnDest rest 0) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka scheduleStartPath
  · exact hcode
  · exact hfork
  · exact run_scheduleStart s msgOff returnDest rest hstack hrun
  · exact hrun
  · exact hnp

/-- Complete sixteen-word schedule trace factored over a `readLE32` helper
certificate. -/
def gasSteps_schedule_of_readLE (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true)
    (hread : ∀ (i : Nat), i < 16 →
      Challenge.EvmProof.GasSteps
        (readEntry (loopState s msgOff returnDest rest i)
          msgOff returnDest rest i)
        (afterRead (loopState s msgOff returnDest rest i)
          msgOff returnDest rest i)) :
    Challenge.EvmProof.GasSteps (scheduleEntry s msgOff returnDest rest)
      (scheduleReturned (loopState s msgOff returnDest rest 16)
        returnDest rest) := by
  have gstart := gasSteps_scheduleStart s msgOff returnDest rest (by omega)
    hcode hfork hrun hnp
  have gloop := gasSteps_loop_of_readLE s msgOff returnDest rest hstack
    hcode hfork hrun hnp hread
  let q := loopState s msgOff returnDest rest 16
  have hqcode : q.executionEnv.code = referenceBytecode := by simpa [q] using hcode
  have hqfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have hqrun : q.halt = .Running := by simpa [q] using hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  have gcondition : Challenge.EvmProof.GasSteps
      (loopAt q msgOff returnDest rest 16)
      (afterExitCondition q msgOff returnDest rest) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka conditionPath
    · exact hqcode
    · exact hqfork
    · exact run_condition_exit q msgOff returnDest rest (by omega) hqcode hqrun
    · exact hqrun
    · exact hqnp
  have gcondition' : Challenge.EvmProof.GasSteps q
      (afterExitCondition q msgOff returnDest rest) :=
    Challenge.EvmProof.GasSteps.cast gcondition (by simp [q]) rfl
  have gexit : Challenge.EvmProof.GasSteps
      (afterExitCondition q msgOff returnDest rest)
      (scheduleReturned q returnDest rest) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka exitPath
    · exact hqcode
    · exact hqfork
    · exact run_exit q msgOff returnDest rest (by omega) hqcode hqrun hreturn
    · exact hqrun
    · exact hqnp
  exact gstart.trans <| gloop.trans <| gcondition'.trans gexit

/-- Unconditional direct trace of the complete compiled `schedule(msgOff)`
function, including all four `BYTE` instructions in each `readLE32` call. -/
def gasSteps_schedule (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (scheduleEntry s msgOff returnDest rest)
      (scheduleReturned (loopState s msgOff returnDest rest 16)
        returnDest rest) := by
  apply gasSteps_schedule_of_readLE s msgOff returnDest rest hstack
    hcode hfork hrun hnp hreturn
  intro i hi
  let q := loopState s msgOff returnDest rest i
  have hqcode : q.executionEnv.code = referenceBytecode := by simpa [q] using hcode
  have hqfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have hqrun : q.halt = .Running := by simpa [q] using hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  simpa [q] using gasSteps_readLE q msgOff returnDest rest i hstack
    hqcode hqfork hqrun hqnp

end Challenge.Ripemd160.Reference.Proofs.Bytecode.Schedule
