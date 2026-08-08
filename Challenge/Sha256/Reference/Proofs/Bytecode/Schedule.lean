import Challenge.Sha256.Reference.Proofs.Bytecode.Functions
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# Direct reference-bytecode proof of the SHA message schedule

The two bytecode loops are proved with indexed memory invariants.  The first
loads sixteen big-endian words from the padded message; the second derives the
remaining forty-eight words with the SHA recurrence.
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

@[simp] private theorem succSmall (n : Nat) (h : n + 1 < 2 ^ 256) :
    (UInt256.ofNat n).succ = UInt256.ofNat (n + 1) :=
  Challenge.EvmProof.Word.succ_ofNat h

@[simp] private theorem addSmall (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.EvmProof.Word.ofNat_add_ofNat h

def firstConditionPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨327, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨328, .push ⟨1, by decide⟩ (UInt256.ofNat 16), by rfl, by decide⟩,
   ⟨329, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨330, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨331, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨332, .push ⟨2, by decide⟩ (UInt256.ofNat 491), by rfl, by decide⟩,
   ⟨333, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def firstLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨334, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨335, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨336, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨337, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨338, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨339, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨340, .push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨341, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩]

def firstStorePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨342, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨343, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨344, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨345, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨346, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨347, .push ⟨2, by decide⟩ (UInt256.ofNat 800), by rfl, by decide⟩,
   ⟨348, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨349, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨350, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨351, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩]

def firstIncrementPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨352, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨353, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨354, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨355, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨356, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨357, .push ⟨2, by decide⟩ (UInt256.ofNat 448), by rfl, by decide⟩,
   ⟨358, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def loadOffset (msgOff : UInt256) (j : Nat) : Nat :=
  (UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 2) + msgOff).toNat

def initialWord (memory : ByteArray) (msgOff : UInt256) (j : Nat) : UInt256 :=
  UInt256.shiftRight (MachineState.readWord memory (loadOffset msgOff j))
    (UInt256.ofNat 224)

def scheduleSlot (j : Nat) : Nat :=
  Accessors.slotOffset 800 (UInt256.ofNat j)

def firstAt (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { s with
    pc := UInt256.ofNat 448
    stack := [UInt256.ofNat j, msgOff, returnDest] ++ rest }

def afterFirstCondition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { s with
    pc := UInt256.ofNat 458
    stack := [UInt256.ofNat j, msgOff, returnDest] ++ rest }

def afterFirstLoad (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { s with
    pc := UInt256.ofNat 468
    stack := [initialWord s.memory msgOff j, UInt256.ofNat j,
      msgOff, returnDest] ++ rest
    activeWords := s.activeWordsAfterUInt256 (loadOffset msgOff j) 32 }

def afterFirstStore (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let loaded := afterFirstLoad s msgOff returnDest rest j
  { loaded with
    pc := UInt256.ofNat 481
    stack := [UInt256.ofNat j, msgOff, returnDest] ++ rest
    memory := MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded (initialWord s.memory msgOff j).toNat 32)
      (scheduleSlot j)
    activeWords := loaded.activeWordsAfterUInt256 (scheduleSlot j) 32 }

def afterFirstIteration (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { afterFirstStore s msgOff returnDest rest j with
    pc := UInt256.ofNat 448
    stack := [UInt256.ofNat (j + 1), msgOff, returnDest] ++ rest }

@[simp] private theorem firstPC (i : Nat) (hlo : 327 ≤ i) (hhi : i ≤ 358) :
    Artifact.referenceArtifact.instructionPC i =
      [448, 449, 451, 452, 453, 454, 457, 458, 459, 461, 462,
       463, 464, 465, 467, 468, 469, 470, 471, 473, 474, 477,
       478, 479, 480, 481, 483, 484, 485, 486, 487, 490][i - 327]! := by
  interval_cases i <;> decide

set_option linter.unusedSimpArgs false in
theorem run_firstCondition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 16)
    (hstack : rest.length < 1019)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock firstConditionPath
      (firstAt s msgOff returnDest rest j) =
        some (afterFirstCondition s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hjWord : (UInt256.ofNat j).toNat = j := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlt : UInt256.lt (UInt256.ofNat j) (UInt256.ofNat 16) =
      UInt256.ofNat 1 := by
    simp [UInt256.lt, hjWord, Challenge.EvmProof.Word.word_toNat_ofNat, hj]
  have hzero : UInt256.isZero (UInt256.ofNat 1) = 0 := by decide
  have htrue : UInt256.isTrue (0 : UInt256) = false := by decide
  simp [firstConditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    firstAt, afterFirstCondition, hc3, hc4, hc5, hrun, hlt, hzero,
    htrue]

set_option linter.unusedSimpArgs false in
theorem run_firstLoad (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hstack : rest.length < 1018)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock firstLoadPath
      (afterFirstCondition s msgOff returnDest rest j) =
        some (afterFirstLoad s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hoff : msgOff + UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 2) =
      UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 2) + msgOff :=
    Challenge.EvmProof.Word.word_add_comm _ _
  simp [firstLoadPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterFirstCondition, afterFirstLoad, initialWord, loadOffset, List.exchange,
    hc3, hc4, hc5, hc6, hrun, hoff, State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_firstStore (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hstack : rest.length < 1016)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock firstStorePath
      (afterFirstLoad s msgOff returnDest rest j) =
        some (afterFirstStore s msgOff returnDest rest j) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hoff : UInt256.ofNat 800 +
        UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 5) =
      UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 5) +
        UInt256.ofNat 800 := Challenge.EvmProof.Word.word_add_comm _ _
  simp [firstStorePath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterFirstLoad, afterFirstStore, scheduleSlot, Accessors.slotOffset,
    List.exchange, hc4, hc5, hc6, hc7, hc8, hrun, hoff,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_firstIncrement (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 16)
    (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock firstIncrementPath
      (afterFirstStore s msgOff returnDest rest j) =
        some (afterFirstIteration s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hadd : UInt256.ofNat j + UInt256.ofNat 1 =
      UInt256.ofNat (j + 1) := Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hdest : Decode.isValidJumpDest referenceBytecode 448 = true := by decide
  simp [firstIncrementPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterFirstStore, afterFirstIteration, afterFirstLoad, List.exchange,
    hc3, hc4, hc5, hcode, hrun, hadd, hdest]

def gasSteps_firstIteration (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 16)
    (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (firstAt s msgOff returnDest rest j)
      (afterFirstIteration s msgOff returnDest rest j) := by
  have gCondition : Challenge.EvmProof.GasSteps
      (firstAt s msgOff returnDest rest j)
      (afterFirstCondition s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka firstConditionPath
    · exact hcode
    · exact hfork
    · exact run_firstCondition s msgOff returnDest rest j hj (by omega) hrun
    · exact hrun
    · exact hnp
  have gLoad : Challenge.EvmProof.GasSteps
      (afterFirstCondition s msgOff returnDest rest j)
      (afterFirstLoad s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka firstLoadPath
    · exact hcode
    · exact hfork
    · exact run_firstLoad s msgOff returnDest rest j (by omega) hrun
    · exact hrun
    · exact hnp
  have gStore : Challenge.EvmProof.GasSteps
      (afterFirstLoad s msgOff returnDest rest j)
      (afterFirstStore s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka firstStorePath
    · exact hcode
    · exact hfork
    · exact run_firstStore s msgOff returnDest rest j hstack hrun
    · exact hrun
    · exact hnp
  have gIncrement : Challenge.EvmProof.GasSteps
      (afterFirstStore s msgOff returnDest rest j)
      (afterFirstIteration s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka firstIncrementPath
    · exact hcode
    · exact hfork
    · exact run_firstIncrement s msgOff returnDest rest j hj (by omega)
        hcode hrun
    · exact hrun
    · exact hnp
  exact gCondition.trans (gLoad.trans (gStore.trans gIncrement))

def firstLoopState (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : Nat → State
  | 0 => firstAt s msgOff returnDest rest 0
  | j + 1 => afterFirstIteration
      (firstLoopState s msgOff returnDest rest j) msgOff returnDest rest j

@[simp] theorem firstLoopState_executionEnv (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    (firstLoopState s msgOff returnDest rest j).executionEnv = s.executionEnv := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp [firstLoopState, afterFirstIteration, afterFirstStore,
        afterFirstLoad, ih]

@[simp] theorem firstLoopState_halt (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    (firstLoopState s msgOff returnDest rest j).halt = s.halt := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp [firstLoopState, afterFirstIteration, afterFirstStore,
        afterFirstLoad, ih]

@[simp] theorem firstLoopState_callStack (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    (firstLoopState s msgOff returnDest rest j).callStack = s.callStack := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp [firstLoopState, afterFirstIteration, afterFirstStore,
        afterFirstLoad, ih]

@[simp] theorem firstAt_firstLoopState (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    firstAt (firstLoopState s msgOff returnDest rest j)
      msgOff returnDest rest j = firstLoopState s msgOff returnDest rest j := by
  cases j <;> rfl

def gasSteps_firstLoop (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (firstLoopState s msgOff returnDest rest 0)
      (firstLoopState s msgOff returnDest rest 16) := by
  apply Challenge.EvmProof.GasSteps.iterateBounded (count := 16)
  intro j hj
  let q := firstLoopState s msgOff returnDest rest j
  have hqcode : q.executionEnv.code = referenceBytecode := by
    simpa [q] using hcode
  have hqfork : q.fork = .Osaka := by
    simpa [q, State.fork] using hfork
  have hqrun : q.halt = .Running := by
    simpa [q] using hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by
    simpa [q] using hnp
  have g := gasSteps_firstIteration q msgOff returnDest rest j hj hstack
    hqcode hqfork hqrun hqnp
  have hs : firstAt q msgOff returnDest rest j =
      firstLoopState s msgOff returnDest rest j := by
    simp [q]
  have ht : afterFirstIteration q msgOff returnDest rest j =
      firstLoopState s msgOff returnDest rest (j + 1) := by
    simp [q, firstLoopState]
  exact Challenge.EvmProof.GasSteps.cast g hs ht

def scheduleEntry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 446
    stack := [msgOff, returnDest] ++ rest }

def scheduleStartPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨325, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨326, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩]

@[simp] private theorem pc325 : Artifact.referenceArtifact.instructionPC 325 = 446 := by decide
@[simp] private theorem pc326 : Artifact.referenceArtifact.instructionPC 326 = 447 := by decide

theorem run_scheduleStart (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock scheduleStartPath
      (scheduleEntry s msgOff returnDest rest) =
        some (firstLoopState s msgOff returnDest rest 0) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  simp [scheduleStartPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    scheduleEntry, firstLoopState, firstAt, hc2, hrun]
  rfl

def gasSteps_scheduleStart (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (scheduleEntry s msgOff returnDest rest)
      (firstLoopState s msgOff returnDest rest 0) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka scheduleStartPath
  · exact hcode
  · exact hfork
  · exact run_scheduleStart s msgOff returnDest rest hstack hrun
  · exact hrun
  · exact hnp

/-! ## W[16..63] recurrence -/

def secondConditionPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨362, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨363, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨364, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨365, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨366, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨367, .push ⟨2, by decide⟩ (UInt256.ofNat 603), by rfl, by decide⟩,
   ⟨368, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def setupW16Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨369, .push ⟨2, by decide⟩ (UInt256.ofNat 592), by rfl, by decide⟩,
   ⟨370, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨371, .push ⟨2, by decide⟩ (UInt256.ofNat 525), by rfl, by decide⟩,
   ⟨372, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨373, .push ⟨1, by decide⟩ (UInt256.ofNat 16), by rfl, by decide⟩,
   ⟨374, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨375, .op .SUB, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨376, .push ⟨2, by decide⟩ (UInt256.ofNat 279), by rfl, by decide⟩,
   ⟨377, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setupW15Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨378, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨379, .push ⟨2, by decide⟩ (UInt256.ofNat 547), by rfl, by decide⟩,
   ⟨380, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨381, .push ⟨2, by decide⟩ (UInt256.ofNat 542), by rfl, by decide⟩,
   ⟨382, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨383, .push ⟨1, by decide⟩ (UInt256.ofNat 15), by rfl, by decide⟩,
   ⟨384, .op (.Dup ⟨8, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨385, .op .SUB, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨386, .push ⟨2, by decide⟩ (UInt256.ofNat 279), by rfl, by decide⟩,
   ⟨387, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setupSsig0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨388, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨389, .push ⟨2, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨390, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setupW7Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨391, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨392, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨393, .push ⟨2, by decide⟩ (UInt256.ofNat 561), by rfl, by decide⟩,
   ⟨394, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨395, .push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨396, .op (.Dup ⟨6, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨397, .op .SUB, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨398, .push ⟨2, by decide⟩ (UInt256.ofNat 279), by rfl, by decide⟩,
   ⟨399, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setupW2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨400, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨401, .push ⟨2, by decide⟩ (UInt256.ofNat 583), by rfl, by decide⟩,
   ⟨402, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨403, .push ⟨2, by decide⟩ (UInt256.ofNat 578), by rfl, by decide⟩,
   ⟨404, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨405, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨406, .op (.Dup ⟨9, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨407, .op .SUB, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨408, .push ⟨2, by decide⟩ (UInt256.ofNat 279), by rfl, by decide⟩,
   ⟨409, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setupSsig1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨410, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨411, .push ⟨2, by decide⟩ (UInt256.ofNat 73), by rfl, by decide⟩,
   ⟨412, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def finishRecurrencePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨413, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨414, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨415, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨416, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨417, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨418, .push ⟨2, by decide⟩ (UInt256.ofNat 299), by rfl, by decide⟩,
   ⟨419, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def secondIncrementPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨420, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨421, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨422, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨423, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨424, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨425, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨426, .push ⟨2, by decide⟩ (UInt256.ofNat 495), by rfl, by decide⟩,
   ⟨427, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem secondPC (i : Nat) (hlo : 362 ≤ i) (hhi : i ≤ 427) :
    Artifact.referenceArtifact.instructionPC i =
      [495,496,498,499,500,501,504,505,508,513,516,517,519,520,521,524,
       525,526,529,530,533,534,536,537,538,541,542,543,546,547,548,549,
       552,553,555,556,557,560,561,562,565,566,569,570,572,573,574,577,
       578,579,582,583,584,585,586,587,588,591,592,593,595,596,597,598,
       599,602][i - 362]! := by
  interval_cases i <;> decide

def wValue (s : State) (j : Nat) : UInt256 :=
  MachineState.readWord s.memory (scheduleSlot j)

def secondAt (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { s with
    pc := UInt256.ofNat 495
    stack := [UInt256.ofNat j, msgOff, returnDest] ++ rest }

def afterSecondCondition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { s with
    pc := UInt256.ofNat 505
    stack := [UInt256.ofNat j, msgOff, returnDest] ++ rest }

def callW16 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadEntry s 279 (UInt256.ofNat (j - 16)) 0 (UInt256.ofNat 525)
    ([UInt256.ofNat 0xffffffff, UInt256.ofNat 592, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def gotW16 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadReturned s 800 (UInt256.ofNat (j - 16)) (UInt256.ofNat 525)
    ([UInt256.ofNat 0xffffffff, UInt256.ofNat 592, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def callW15 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := gotW16 s msgOff returnDest rest j
  Accessors.loadEntry q 279 (UInt256.ofNat (j - 15)) 0 (UInt256.ofNat 542)
    ([0, UInt256.ofNat 547, wValue s (j - 16), UInt256.ofNat 0xffffffff,
      UInt256.ofNat 592, UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotW15 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := gotW16 s msgOff returnDest rest j
  Accessors.loadReturned q 800 (UInt256.ofNat (j - 15)) (UInt256.ofNat 542)
    ([0, UInt256.ofNat 547, wValue s (j - 16), UInt256.ofNat 0xffffffff,
      UInt256.ofNat 592, UInt256.ofNat j, msgOff, returnDest] ++ rest)

def callSsig0 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := gotW15 s msgOff returnDest rest j
  Functions.unaryEntry q 32 (wValue q (j - 15)) 0 (UInt256.ofNat 547)
    ([wValue s (j - 16), UInt256.ofNat 0xffffffff, UInt256.ofNat 592,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotSsig0 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := gotW15 s msgOff returnDest rest j
  Functions.unaryReturned q (Word.evmSmallSigma0 (wValue q (j - 15)))
    (UInt256.ofNat 547)
    ([wValue s (j - 16), UInt256.ofNat 0xffffffff, UInt256.ofNat 592,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def firstSum (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : UInt256 :=
  let q := gotW15 s msgOff returnDest rest j
  Word.evmSmallSigma0 (wValue q (j - 15)) + wValue s (j - 16)

def callW7 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := gotSsig0 s msgOff returnDest rest j
  Accessors.loadEntry q 279 (UInt256.ofNat (j - 7)) 0 (UInt256.ofNat 561)
    ([firstSum s msgOff returnDest rest j, UInt256.ofNat 0xffffffff,
      UInt256.ofNat 592, UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotW7 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := gotSsig0 s msgOff returnDest rest j
  Accessors.loadReturned q 800 (UInt256.ofNat (j - 7)) (UInt256.ofNat 561)
    ([firstSum s msgOff returnDest rest j, UInt256.ofNat 0xffffffff,
      UInt256.ofNat 592, UInt256.ofNat j, msgOff, returnDest] ++ rest)

def callW2 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := gotW7 s msgOff returnDest rest j
  Accessors.loadEntry q 279 (UInt256.ofNat (j - 2)) 0 (UInt256.ofNat 578)
    ([0, UInt256.ofNat 583, wValue q (j - 7),
      firstSum s msgOff returnDest rest j, UInt256.ofNat 0xffffffff,
      UInt256.ofNat 592, UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotW2 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := gotW7 s msgOff returnDest rest j
  Accessors.loadReturned q 800 (UInt256.ofNat (j - 2)) (UInt256.ofNat 578)
    ([0, UInt256.ofNat 583, wValue q (j - 7),
      firstSum s msgOff returnDest rest j, UInt256.ofNat 0xffffffff,
      UInt256.ofNat 592, UInt256.ofNat j, msgOff, returnDest] ++ rest)

def callSsig1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := gotW2 s msgOff returnDest rest j
  Functions.unaryEntry q 73 (wValue q (j - 2)) 0 (UInt256.ofNat 583)
    ([wValue (gotW7 s msgOff returnDest rest j) (j - 7),
      firstSum s msgOff returnDest rest j, UInt256.ofNat 0xffffffff,
      UInt256.ofNat 592, UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotSsig1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := gotW2 s msgOff returnDest rest j
  Functions.unaryReturned q (Word.evmSmallSigma1 (wValue q (j - 2)))
    (UInt256.ofNat 583)
    ([wValue (gotW7 s msgOff returnDest rest j) (j - 7),
      firstSum s msgOff returnDest rest j, UInt256.ofNat 0xffffffff,
      UInt256.ofNat 592, UInt256.ofNat j, msgOff, returnDest] ++ rest)

def recurrenceWord (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : UInt256 :=
  let q2 := gotW2 s msgOff returnDest rest j
  let q7 := gotW7 s msgOff returnDest rest j
  Challenge.EvmProof.Word.mask32
    ((Word.evmSmallSigma1 (wValue q2 (j - 2)) + wValue q7 (j - 7)) +
      firstSum s msgOff returnDest rest j)

def callWSet (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := gotSsig1 s msgOff returnDest rest j
  Accessors.storeEntry q 299 (UInt256.ofNat j)
    (recurrenceWord s msgOff returnDest rest j) (UInt256.ofNat 592)
    ([UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotWSet (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := gotSsig1 s msgOff returnDest rest j
  Accessors.storeReturned q 800 (UInt256.ofNat j)
    (recurrenceWord s msgOff returnDest rest j) (UInt256.ofNat 592)
    ([UInt256.ofNat j, msgOff, returnDest] ++ rest)

def afterSecondIteration (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  secondAt (gotWSet s msgOff returnDest rest j)
    msgOff returnDest rest (j + 1)

set_option linter.unusedSimpArgs false in
theorem run_secondCondition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj16 : 16 ≤ j) (hj64 : j < 64)
    (hstack : rest.length < 1019) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock secondConditionPath
      (secondAt s msgOff returnDest rest j) =
        some (afterSecondCondition s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hjWord : (UInt256.ofNat j).toNat = j := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlt : UInt256.lt (UInt256.ofNat j) (UInt256.ofNat 64) =
      UInt256.ofNat 1 := by
    simp [UInt256.lt, hjWord, Challenge.EvmProof.Word.word_toNat_ofNat, hj64]
  have hzero : UInt256.isZero (UInt256.ofNat 1) = 0 := by decide
  have htrue : UInt256.isTrue (0 : UInt256) = false := by decide
  simp [secondConditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    secondAt, afterSecondCondition, hc3, hc4, hc5, hrun, hlt, hzero, htrue]

set_option linter.unusedSimpArgs false in
theorem run_setupW16 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj16 : 16 ≤ j) (hj64 : j < 64)
    (hstack : rest.length < 1014)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupW16Path
      (afterSecondCondition s msgOff returnDest rest j) =
        some (callW16 s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hj16 (by omega : j < 2 ^ 256)
  have hdest : Decode.isValidJumpDest referenceBytecode 279 = true := by decide
  simp [setupW16Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterSecondCondition, callW16, Accessors.loadEntry, List.exchange,
    hc3, hc4, hc5, hc6, hc7, hc8, hc9, hcode, hrun, hsub, hdest]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_setupW15 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj16 : 16 ≤ j) (hj64 : j < 64)
    (hstack : rest.length < 1011)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupW15Path
      (gotW16 s msgOff returnDest rest j) =
        some (callW15 s msgOff returnDest rest j) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega : 15 ≤ j)
    (by omega : j < 2 ^ 256)
  have hdest : Decode.isValidJumpDest referenceBytecode 279 = true := by decide
  simp [setupW15Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotW16, callW15, wValue, Accessors.loadEntry, Accessors.loadReturned,
    scheduleSlot, List.exchange, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hcode, hrun,
    hsub, hdest]
  constructor

set_option linter.unusedSimpArgs false in
theorem run_setupSsig0 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hstack : rest.length < 1014)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupSsig0Path
      (gotW15 s msgOff returnDest rest j) =
        some (callSsig0 s msgOff returnDest rest j) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 32 = true := by decide
  simp [setupSsig0Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotW15, gotW16, callSsig0, wValue, scheduleSlot, Functions.unaryEntry,
    Accessors.loadReturned, List.exchange, hc7, hc8, hc9, hc10, hcode, hrun,
    hdest]

set_option linter.unusedSimpArgs false in
theorem run_setupW7 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj16 : 16 ≤ j) (hj64 : j < 64)
    (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupW7Path
      (gotSsig0 s msgOff returnDest rest j) =
        some (callW7 s msgOff returnDest rest j) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega : 7 ≤ j)
    (by omega : j < 2 ^ 256)
  have hdest : Decode.isValidJumpDest referenceBytecode 279 = true := by decide
  simp [setupW7Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotSsig0, gotW15, gotW16, callW7, firstSum, wValue, scheduleSlot,
    Functions.unaryReturned, Accessors.loadReturned, Accessors.loadEntry,
    List.exchange, hc6, hc7, hc8, hc9, hc10, hc11, hcode, hrun, hsub, hdest]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_setupW2 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj16 : 16 ≤ j) (hj64 : j < 64)
    (hstack : rest.length < 1009)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupW2Path
      (gotW7 s msgOff returnDest rest j) =
        some (callW2 s msgOff returnDest rest j) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega : 2 ≤ j)
    (by omega : j < 2 ^ 256)
  have hdest : Decode.isValidJumpDest referenceBytecode 279 = true := by decide
  simp [setupW2Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotW7, gotSsig0, gotW15, gotW16, callW2, firstSum, wValue,
    scheduleSlot, Functions.unaryReturned, Accessors.loadReturned,
    Accessors.loadEntry, List.exchange, hc7, hc8, hc9, hc10, hc11, hc12,
    hc13, hc14, hcode, hrun, hsub, hdest]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_setupSsig1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hstack : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupSsig1Path
      (gotW2 s msgOff returnDest rest j) =
        some (callSsig1 s msgOff returnDest rest j) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 73 = true := by decide
  simp [setupSsig1Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotW2, gotW7, gotSsig0, gotW15, gotW16, callSsig1, firstSum,
    wValue, scheduleSlot, Functions.unaryEntry, Functions.unaryReturned,
    Accessors.loadReturned, List.exchange, hc10, hc11, hc12, hcode, hrun,
    hdest]

set_option linter.unusedSimpArgs false in
theorem run_finishRecurrence (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hstack : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock finishRecurrencePath
      (gotSsig1 s msgOff returnDest rest j) =
        some (callWSet s msgOff returnDest rest j) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 299 = true := by decide
  simp [finishRecurrencePath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotSsig1, gotW2, gotW7, gotSsig0, gotW15, gotW16, callWSet,
    recurrenceWord, firstSum, wValue, scheduleSlot, Challenge.EvmProof.Word.mask32,
    Functions.unaryReturned, Accessors.storeEntry, Accessors.loadReturned,
    List.exchange, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10,
    hc11, hc12, hcode, hrun, hdest]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_secondIncrement (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj64 : j < 64)
    (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock secondIncrementPath
      (gotWSet s msgOff returnDest rest j) =
        some (afterSecondIteration s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hadd : UInt256.ofNat j + UInt256.ofNat 1 =
      UInt256.ofNat (j + 1) := Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hdest : Decode.isValidJumpDest referenceBytecode 495 = true := by decide
  simp [secondIncrementPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotWSet, gotSsig1, gotW2, gotW7, gotSsig0, gotW15, gotW16,
    afterSecondIteration, secondAt, Accessors.storeReturned,
    Functions.unaryReturned, Accessors.loadReturned, List.exchange,
    hc3, hc4, hc5, hcode, hrun, hadd, hdest]

def gasSteps_secondIteration (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj16 : 16 ≤ j) (hj64 : j < 64)
    (hstack : rest.length < 990)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (secondAt s msgOff returnDest rest j)
      (afterSecondIteration s msgOff returnDest rest j) := by
  have rawCondition : Challenge.EvmProof.GasSteps
      (secondAt s msgOff returnDest rest j)
      (afterSecondCondition s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka secondConditionPath
    · exact hcode
    · exact hfork
    · exact run_secondCondition s msgOff returnDest rest j hj16 hj64
        (by omega) hrun
    · exact hrun
    · exact hnp
  have rawW16 : Challenge.EvmProof.GasSteps
      (afterSecondCondition s msgOff returnDest rest j)
      (callW16 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupW16Path
    · exact hcode
    · exact hfork
    · exact run_setupW16 s msgOff returnDest rest j hj16 hj64
        (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have call16 : Challenge.EvmProof.GasSteps
      (callW16 s msgOff returnDest rest j)
      (gotW16 s msgOff returnDest rest j) := by
    exact Accessors.gasSteps_wAt s (UInt256.ofNat (j - 16)) 0
      (UInt256.ofNat 525)
      ([UInt256.ofNat 0xffffffff, UInt256.ofNat 592, UInt256.ofNat j,
        msgOff, returnDest] ++ rest)
      (by simp; omega) hcode hfork hrun hnp (by decide)
  let q16 := gotW16 s msgOff returnDest rest j
  have q16code : q16.executionEnv.code = referenceBytecode := by
    simpa [q16, gotW16, Accessors.loadReturned] using hcode
  have q16fork : q16.fork = .Osaka := by
    simpa [q16, gotW16, Accessors.loadReturned, State.fork] using hfork
  have q16run : q16.halt = .Running := by
    simpa [q16, gotW16, Accessors.loadReturned] using hrun
  have q16np : Precompile.isPrecompileWithConfig q16.executionEnv.precompileConfig q16.executionEnv.fork
      q16.executionEnv.codeAddr = false := by
    simpa [q16, gotW16, Accessors.loadReturned] using hnp
  have rawW15 : Challenge.EvmProof.GasSteps
      (gotW16 s msgOff returnDest rest j)
      (callW15 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupW15Path
    · exact q16code
    · exact q16fork
    · exact run_setupW15 s msgOff returnDest rest j hj16 hj64
        (by omega) hcode hrun
    · exact q16run
    · exact q16np
  have call15 : Challenge.EvmProof.GasSteps
      (callW15 s msgOff returnDest rest j)
      (gotW15 s msgOff returnDest rest j) := by
    exact Accessors.gasSteps_wAt q16 (UInt256.ofNat (j - 15)) 0
      (UInt256.ofNat 542)
      ([0, UInt256.ofNat 547, wValue s (j - 16), UInt256.ofNat 0xffffffff,
        UInt256.ofNat 592, UInt256.ofNat j, msgOff, returnDest] ++ rest)
      (by simp; omega) q16code q16fork q16run q16np (by decide)
  let q15 := gotW15 s msgOff returnDest rest j
  have q15code : q15.executionEnv.code = referenceBytecode := by
    simpa [q15, gotW15, q16, Accessors.loadReturned] using q16code
  have q15fork : q15.fork = .Osaka := by
    simpa [q15, gotW15, q16, Accessors.loadReturned, State.fork] using q16fork
  have q15run : q15.halt = .Running := by
    simpa [q15, gotW15, q16, Accessors.loadReturned] using q16run
  have q15np : Precompile.isPrecompileWithConfig q15.executionEnv.precompileConfig q15.executionEnv.fork
      q15.executionEnv.codeAddr = false := by
    simpa [q15, gotW15, q16, Accessors.loadReturned] using q16np
  have rawS0 : Challenge.EvmProof.GasSteps
      (gotW15 s msgOff returnDest rest j)
      (callSsig0 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupSsig0Path
    · exact q15code
    · exact q15fork
    · exact run_setupSsig0 s msgOff returnDest rest j (by omega) hcode hrun
    · exact q15run
    · exact q15np
  have callS0 : Challenge.EvmProof.GasSteps
      (callSsig0 s msgOff returnDest rest j)
      (gotSsig0 s msgOff returnDest rest j) := by
    exact Functions.gasSteps_ssig0 q15 (wValue q15 (j - 15)) 0
      (UInt256.ofNat 547)
      ([wValue s (j - 16), UInt256.ofNat 0xffffffff, UInt256.ofNat 592,
        UInt256.ofNat j, msgOff, returnDest] ++ rest)
      (by simp; omega) q15code q15fork q15run q15np (by decide)
  let qs0 := gotSsig0 s msgOff returnDest rest j
  have qs0code : qs0.executionEnv.code = referenceBytecode := by
    simpa [qs0, gotSsig0, q15, Functions.unaryReturned] using q15code
  have qs0fork : qs0.fork = .Osaka := by
    simpa [qs0, gotSsig0, q15, Functions.unaryReturned, State.fork] using q15fork
  have qs0run : qs0.halt = .Running := by
    simpa [qs0, gotSsig0, q15, Functions.unaryReturned] using q15run
  have qs0np : Precompile.isPrecompileWithConfig qs0.executionEnv.precompileConfig qs0.executionEnv.fork
      qs0.executionEnv.codeAddr = false := by
    simpa [qs0, gotSsig0, q15, Functions.unaryReturned] using q15np
  have rawW7 : Challenge.EvmProof.GasSteps
      (gotSsig0 s msgOff returnDest rest j)
      (callW7 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupW7Path
    · exact qs0code
    · exact qs0fork
    · exact run_setupW7 s msgOff returnDest rest j hj16 hj64
        (by omega) hcode hrun
    · exact qs0run
    · exact qs0np
  have call7 : Challenge.EvmProof.GasSteps
      (callW7 s msgOff returnDest rest j)
      (gotW7 s msgOff returnDest rest j) := by
    exact Accessors.gasSteps_wAt qs0 (UInt256.ofNat (j - 7)) 0
      (UInt256.ofNat 561)
      ([firstSum s msgOff returnDest rest j, UInt256.ofNat 0xffffffff,
        UInt256.ofNat 592, UInt256.ofNat j, msgOff, returnDest] ++ rest)
      (by simp; omega) qs0code qs0fork qs0run qs0np (by decide)
  let q7 := gotW7 s msgOff returnDest rest j
  have q7code : q7.executionEnv.code = referenceBytecode := by
    simpa [q7, gotW7, qs0, Accessors.loadReturned] using qs0code
  have q7fork : q7.fork = .Osaka := by
    simpa [q7, gotW7, qs0, Accessors.loadReturned, State.fork] using qs0fork
  have q7run : q7.halt = .Running := by
    simpa [q7, gotW7, qs0, Accessors.loadReturned] using qs0run
  have q7np : Precompile.isPrecompileWithConfig q7.executionEnv.precompileConfig q7.executionEnv.fork
      q7.executionEnv.codeAddr = false := by
    simpa [q7, gotW7, qs0, Accessors.loadReturned] using qs0np
  have rawW2 : Challenge.EvmProof.GasSteps
      (gotW7 s msgOff returnDest rest j)
      (callW2 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupW2Path
    · exact q7code
    · exact q7fork
    · exact run_setupW2 s msgOff returnDest rest j hj16 hj64
        (by omega) hcode hrun
    · exact q7run
    · exact q7np
  have call2 : Challenge.EvmProof.GasSteps
      (callW2 s msgOff returnDest rest j)
      (gotW2 s msgOff returnDest rest j) := by
    exact Accessors.gasSteps_wAt q7 (UInt256.ofNat (j - 2)) 0
      (UInt256.ofNat 578)
      ([0, UInt256.ofNat 583, wValue q7 (j - 7),
        firstSum s msgOff returnDest rest j, UInt256.ofNat 0xffffffff,
        UInt256.ofNat 592, UInt256.ofNat j, msgOff, returnDest] ++ rest)
      (by simp; omega) q7code q7fork q7run q7np (by decide)
  let q2 := gotW2 s msgOff returnDest rest j
  have q2code : q2.executionEnv.code = referenceBytecode := by
    simpa [q2, gotW2, q7, Accessors.loadReturned] using q7code
  have q2fork : q2.fork = .Osaka := by
    simpa [q2, gotW2, q7, Accessors.loadReturned, State.fork] using q7fork
  have q2run : q2.halt = .Running := by
    simpa [q2, gotW2, q7, Accessors.loadReturned] using q7run
  have q2np : Precompile.isPrecompileWithConfig q2.executionEnv.precompileConfig q2.executionEnv.fork
      q2.executionEnv.codeAddr = false := by
    simpa [q2, gotW2, q7, Accessors.loadReturned] using q7np
  have rawS1 : Challenge.EvmProof.GasSteps
      (gotW2 s msgOff returnDest rest j)
      (callSsig1 s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setupSsig1Path
    · exact q2code
    · exact q2fork
    · exact run_setupSsig1 s msgOff returnDest rest j (by omega) hcode hrun
    · exact q2run
    · exact q2np
  have callS1 : Challenge.EvmProof.GasSteps
      (callSsig1 s msgOff returnDest rest j)
      (gotSsig1 s msgOff returnDest rest j) := by
    exact Functions.gasSteps_ssig1 q2 (wValue q2 (j - 2)) 0
      (UInt256.ofNat 583)
      ([wValue q7 (j - 7), firstSum s msgOff returnDest rest j,
        UInt256.ofNat 0xffffffff, UInt256.ofNat 592, UInt256.ofNat j,
        msgOff, returnDest] ++ rest)
      (by simp; omega) q2code q2fork q2run q2np (by decide)
  let qs1 := gotSsig1 s msgOff returnDest rest j
  have qs1code : qs1.executionEnv.code = referenceBytecode := by
    simpa [qs1, gotSsig1, q2, Functions.unaryReturned] using q2code
  have qs1fork : qs1.fork = .Osaka := by
    simpa [qs1, gotSsig1, q2, Functions.unaryReturned, State.fork] using q2fork
  have qs1run : qs1.halt = .Running := by
    simpa [qs1, gotSsig1, q2, Functions.unaryReturned] using q2run
  have qs1np : Precompile.isPrecompileWithConfig qs1.executionEnv.precompileConfig qs1.executionEnv.fork
      qs1.executionEnv.codeAddr = false := by
    simpa [qs1, gotSsig1, q2, Functions.unaryReturned] using q2np
  have rawFinish : Challenge.EvmProof.GasSteps
      (gotSsig1 s msgOff returnDest rest j)
      (callWSet s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka finishRecurrencePath
    · exact qs1code
    · exact qs1fork
    · exact run_finishRecurrence s msgOff returnDest rest j (by omega)
        hcode hrun
    · exact qs1run
    · exact qs1np
  have callSet : Challenge.EvmProof.GasSteps
      (callWSet s msgOff returnDest rest j)
      (gotWSet s msgOff returnDest rest j) := by
    exact Accessors.gasSteps_wSet qs1 (UInt256.ofNat j)
      (recurrenceWord s msgOff returnDest rest j) (UInt256.ofNat 592)
      ([UInt256.ofNat j, msgOff, returnDest] ++ rest)
      (by simp; omega) qs1code qs1fork qs1run qs1np (by decide)
  let qset := gotWSet s msgOff returnDest rest j
  have qsetcode : qset.executionEnv.code = referenceBytecode := by
    simpa [qset, gotWSet, qs1, Accessors.storeReturned] using qs1code
  have qsetfork : qset.fork = .Osaka := by
    simpa [qset, gotWSet, qs1, Accessors.storeReturned, State.fork] using qs1fork
  have qsetrun : qset.halt = .Running := by
    simpa [qset, gotWSet, qs1, Accessors.storeReturned] using qs1run
  have qsetnp : Precompile.isPrecompileWithConfig qset.executionEnv.precompileConfig qset.executionEnv.fork
      qset.executionEnv.codeAddr = false := by
    simpa [qset, gotWSet, qs1, Accessors.storeReturned] using qs1np
  have rawIncrement : Challenge.EvmProof.GasSteps
      (gotWSet s msgOff returnDest rest j)
      (afterSecondIteration s msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka secondIncrementPath
    · exact qsetcode
    · exact qsetfork
    · exact run_secondIncrement s msgOff returnDest rest j hj64
        (by omega) hcode hrun
    · exact qsetrun
    · exact qsetnp
  exact rawCondition
    |>.trans rawW16
    |>.trans call16
    |>.trans rawW15
    |>.trans call15
    |>.trans rawS0
    |>.trans callS0
    |>.trans rawW7
    |>.trans call7
    |>.trans rawW2
    |>.trans call2
    |>.trans rawS1
    |>.trans callS1
    |>.trans rawFinish
    |>.trans callSet
    |>.trans rawIncrement

def secondLoopState (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : Nat → State
  | 0 => secondAt s msgOff returnDest rest 16
  | n + 1 => afterSecondIteration
      (secondLoopState s msgOff returnDest rest n)
      msgOff returnDest rest (16 + n)

@[simp] theorem afterSecondIteration_executionEnv (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    (afterSecondIteration s msgOff returnDest rest j).executionEnv =
      s.executionEnv := by
  rfl

@[simp] theorem afterSecondIteration_halt (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    (afterSecondIteration s msgOff returnDest rest j).halt = s.halt := by
  rfl

@[simp] theorem afterSecondIteration_callStack (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    (afterSecondIteration s msgOff returnDest rest j).callStack =
      s.callStack := by
  rfl

@[simp] theorem secondLoopState_executionEnv (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (secondLoopState s msgOff returnDest rest n).executionEnv = s.executionEnv := by
  induction n with
  | zero => rfl
  | succ n ih => simp [secondLoopState, ih]

@[simp] theorem secondLoopState_halt (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (secondLoopState s msgOff returnDest rest n).halt = s.halt := by
  induction n with
  | zero => rfl
  | succ n ih => simp [secondLoopState, ih]

@[simp] theorem secondLoopState_callStack (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (secondLoopState s msgOff returnDest rest n).callStack = s.callStack := by
  induction n with
  | zero => rfl
  | succ n ih => simp [secondLoopState, ih]

@[simp] theorem secondAt_secondLoopState (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    secondAt (secondLoopState s msgOff returnDest rest n)
      msgOff returnDest rest (16 + n) =
        secondLoopState s msgOff returnDest rest n := by
  cases n <;> simp [secondLoopState, afterSecondIteration, secondAt, Nat.add_assoc]

def gasSteps_secondLoop (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 990)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (secondLoopState s msgOff returnDest rest 0)
      (secondLoopState s msgOff returnDest rest 48) := by
  apply Challenge.EvmProof.GasSteps.iterateBounded (count := 48)
  intro n hn
  let q := secondLoopState s msgOff returnDest rest n
  have hqcode : q.executionEnv.code = referenceBytecode := by
    simpa [q] using hcode
  have hqfork : q.fork = .Osaka := by
    simpa [q, State.fork] using hfork
  have hqrun : q.halt = .Running := by
    simpa [q] using hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by
    simpa [q] using hnp
  have g := gasSteps_secondIteration q msgOff returnDest rest (16 + n)
    (by omega) (by omega) hstack hqcode hqfork hqrun hqnp
  have hs : secondAt q msgOff returnDest rest (16 + n) =
      secondLoopState s msgOff returnDest rest n := by
    simp [q]
  have ht : afterSecondIteration q msgOff returnDest rest (16 + n) =
      secondLoopState s msgOff returnDest rest (n + 1) := by
    simp [q, secondLoopState]
  exact Challenge.EvmProof.GasSteps.cast g hs ht

/-! ## Loop exits and the complete schedule subroutine -/

def firstExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  firstConditionPath ++
    [⟨359, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
     ⟨360, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
     ⟨361, .push ⟨1, by decide⟩ (UInt256.ofNat 16), by rfl, by decide⟩]

def secondExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  secondConditionPath ++
    [⟨428, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
     ⟨429, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
     ⟨430, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
     ⟨431, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def scheduleReturned (s : State) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := returnDest, stack := rest }

@[simp] private theorem pc359 : Artifact.referenceArtifact.instructionPC 359 = 491 := by decide
@[simp] private theorem pc360 : Artifact.referenceArtifact.instructionPC 360 = 492 := by decide
@[simp] private theorem pc361 : Artifact.referenceArtifact.instructionPC 361 = 493 := by decide
@[simp] private theorem pc428 : Artifact.referenceArtifact.instructionPC 428 = 603 := by decide
@[simp] private theorem pc429 : Artifact.referenceArtifact.instructionPC 429 = 604 := by decide
@[simp] private theorem pc430 : Artifact.referenceArtifact.instructionPC 430 = 605 := by decide
@[simp] private theorem pc431 : Artifact.referenceArtifact.instructionPC 431 = 606 := by decide

theorem run_firstExit (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock firstExitPath
      (firstAt s msgOff returnDest rest 16) =
        some (secondAt s msgOff returnDest rest 16) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat 16) (UInt256.ofNat 16) = 0 := by decide
  have hzero : UInt256.isZero (0 : UInt256) = UInt256.ofNat 1 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) = true := by decide
  have hdest : Decode.isValidJumpDest referenceBytecode 491 = true := by decide
  simp [firstExitPath, firstConditionPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    firstAt, secondAt, hc2, hc3, hc4, hc5, hcode, hrun, hlt, hzero, htrue, hdest]

def gasSteps_firstExit (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (firstAt s msgOff returnDest rest 16)
      (secondAt s msgOff returnDest rest 16) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka firstExitPath
  · exact hcode
  · exact hfork
  · exact run_firstExit s msgOff returnDest rest hstack hcode hrun
  · exact hrun
  · exact hnp

theorem run_secondExit (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock secondExitPath
      (secondAt s msgOff returnDest rest 64) =
        some (scheduleReturned s returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat 64) (UInt256.ofNat 64) = 0 := by decide
  have hzero : UInt256.isZero (0 : UInt256) = UInt256.ofNat 1 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) = true := by decide
  have hdest : Decode.isValidJumpDest referenceBytecode 603 = true := by decide
  simp [secondExitPath, secondConditionPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    secondAt, scheduleReturned, hc1, hc2, hc3, hc4, hc5, hcode, hrun, hlt, hzero, htrue,
    hdest, hreturn]

def gasSteps_secondExit (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (secondAt s msgOff returnDest rest 64)
      (scheduleReturned s returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka secondExitPath
  · exact hcode
  · exact hfork
  · exact run_secondExit s msgOff returnDest rest hstack hcode hrun hreturn
  · exact hrun
  · exact hnp

def scheduleResult (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  let afterFirst := firstLoopState s msgOff returnDest rest 16
  let afterSecond := secondLoopState afterFirst msgOff returnDest rest 48
  scheduleReturned afterSecond returnDest rest

def gasSteps_schedule (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 990)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (scheduleEntry s msgOff returnDest rest)
      (scheduleResult s msgOff returnDest rest) := by
  let q1 := firstLoopState s msgOff returnDest rest 16
  let q2 := secondLoopState q1 msgOff returnDest rest 48
  have start := gasSteps_scheduleStart s msgOff returnDest rest (by omega)
    hcode hfork hrun hnp
  have first := gasSteps_firstLoop s msgOff returnDest rest (by omega)
    hcode hfork hrun hnp
  have q1code : q1.executionEnv.code = referenceBytecode := by simpa [q1] using hcode
  have q1fork : q1.fork = .Osaka := by simpa [q1, State.fork] using hfork
  have q1run : q1.halt = .Running := by simpa [q1] using hrun
  have q1np : Precompile.isPrecompileWithConfig q1.executionEnv.precompileConfig q1.executionEnv.fork
      q1.executionEnv.codeAddr = false := by simpa [q1] using hnp
  have bridgeRaw := gasSteps_firstExit q1 msgOff returnDest rest (by omega)
    q1code q1fork q1run q1np
  have bridgeStart : firstAt q1 msgOff returnDest rest 16 = q1 := by
    simp [q1]
  have bridge := Challenge.EvmProof.GasSteps.cast bridgeRaw bridgeStart rfl
  have second := gasSteps_secondLoop q1 msgOff returnDest rest hstack
    q1code q1fork q1run q1np
  have q2code : q2.executionEnv.code = referenceBytecode := by simpa [q2] using q1code
  have q2fork : q2.fork = .Osaka := by simpa [q2, State.fork] using q1fork
  have q2run : q2.halt = .Running := by simpa [q2] using q1run
  have q2np : Precompile.isPrecompileWithConfig q2.executionEnv.precompileConfig q2.executionEnv.fork
      q2.executionEnv.codeAddr = false := by simpa [q2] using q1np
  have finishRaw := gasSteps_secondExit q2 msgOff returnDest rest (by omega)
    q2code q2fork q2run q2np hreturn
  have finishStart : secondAt q2 msgOff returnDest rest 64 = q2 := by
    simpa [q2] using
      secondAt_secondLoopState q1 msgOff returnDest rest 48
  have finish := Challenge.EvmProof.GasSteps.cast finishRaw finishStart rfl
  exact start
    |>.trans first
    |>.trans bridge
    |>.trans second
    |>.trans finish

def gasSteps_scheduleCost (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 990)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) : Nat :=
  @Challenge.EvmProof.GasSteps.cost
    (scheduleEntry s msgOff returnDest rest)
    (scheduleResult s msgOff returnDest rest)
    (gasSteps_schedule s msgOff returnDest rest hstack hcode hfork hrun hnp
      hreturn)

end Challenge.Sha256.Reference.Proofs.Bytecode.Schedule
