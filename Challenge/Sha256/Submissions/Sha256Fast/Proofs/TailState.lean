import Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverInvariants

set_option warningAsError true

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailState

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof
open MemoryCorrect

def prepared (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 2514
    activeWords := UInt256.ofNat 140
    memory := MachineState.writeBytes
      (MachineState.writeBytes s.memory
        (MachineState.readPadded s.executionEnv.calldata off.toNat 64) 288)
      (ByteArray.mk #[UInt8.ofNat 128])
      (UInt256.ofNat 288 + rem).toNat
    stack := [UInt256.ofNat 2533,
      UInt256.lt rem (UInt256.ofNat 56), off, endWord, rem, n] ++ rest }

def shortBranch (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) : State :=
  { prepared s off endWord rem n rest with
    pc := UInt256.ofNat 2533
    stack := [off, endWord, rem, n] ++ rest }

def longBranch (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) : State :=
  { prepared s off endWord rem n rest with
    pc := UInt256.ofNat 2515
    stack := [off, endWord, rem, n] ++ rest }

def firstEntry (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) : State :=
  { longBranch s off endWord rem n rest with
    pc := UInt256.ofNat 4
    stack := [UInt256.ofNat 2522, off, endWord, rem, n] ++ rest }

def firstResult (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) : State :=
  CompressionCorrect.finalState (firstEntry s off endWord rem n rest) H
    (UInt256.ofNat 2522) ([off, endWord, rem, n] ++ rest)

def cleared (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) : State :=
  let q := firstResult s H off endWord rem n rest
  { q with
    pc := UInt256.ofNat 2533
    activeWords := UInt256.ofNat 140
    memory := MachineState.writeBytes
      (MachineState.writeBytes q.memory
        (Data.Bytes.natToBytesPadded 0 32) 288)
      (Data.Bytes.natToBytesPadded 0 32) 320 }

def lengthEntry (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 4
    activeWords := UInt256.ofNat 140
    memory := MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded
        (UInt256.shiftLeft
          (UInt256.land (UInt256.ofNat 18446744073709551615)
            (UInt256.shiftLeft n (UInt256.ofNat 3)))
          (UInt256.ofNat 192)).toNat 32) 344
    stack := [UInt256.ofNat 2562, off, endWord, rem, n] ++ rest }

def finalResult (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) : State :=
  CompressionCorrect.finalState (lengthEntry s off endWord rem n rest) H
    (UInt256.ofNat 2562) ([off, endWord, rem, n] ++ rest)

def finalHash (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) : Array UInt32 :=
  Sha256.compressBlock H (lengthEntry s off endWord rem n rest).memory 288

def outputResult (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) : State :=
  let q := finalResult s H off endWord rem n rest
  let F := finalHash s H off endWord rem n rest
  { q with
    pc := UInt256.ofNat 2621
    halt := .Returned
    activeWords := UInt256.ofNat 140
    memory := MachineState.writeBytes q.memory
      (DriverBlocks.outputBytes F[0]! F[1]! F[2]! F[3]!
        F[4]! F[5]! F[6]! F[7]!) 0
    hReturn := DriverBlocks.outputBytes F[0]! F[1]! F[2]! F[3]!
      F[4]! F[5]! F[6]! F[7]!
    stack := [off, endWord, rem, n] ++ rest }

@[simp] theorem prepared_executionEnv (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) :
    (prepared s off endWord rem n rest).executionEnv = s.executionEnv := rfl

@[simp] theorem prepared_halt (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) :
    (prepared s off endWord rem n rest).halt = s.halt := rfl

@[simp] theorem prepared_fork (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) :
    (prepared s off endWord rem n rest).fork = s.fork := rfl

@[simp] theorem shortBranch_executionEnv (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) :
    (shortBranch s off endWord rem n rest).executionEnv = s.executionEnv := rfl

@[simp] theorem shortBranch_halt (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) :
    (shortBranch s off endWord rem n rest).halt = s.halt := rfl

@[simp] theorem shortBranch_fork (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) :
    (shortBranch s off endWord rem n rest).fork = s.fork := rfl

@[simp] theorem shortBranch_callStack (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) :
    (shortBranch s off endWord rem n rest).callStack = s.callStack := rfl

@[simp] theorem longBranch_executionEnv (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) :
    (longBranch s off endWord rem n rest).executionEnv = s.executionEnv := rfl

@[simp] theorem longBranch_halt (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) :
    (longBranch s off endWord rem n rest).halt = s.halt := rfl

@[simp] theorem longBranch_fork (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) :
    (longBranch s off endWord rem n rest).fork = s.fork := rfl

@[simp] theorem firstEntry_executionEnv (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) :
    (firstEntry s off endWord rem n rest).executionEnv = s.executionEnv := rfl

@[simp] theorem firstEntry_halt (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) :
    (firstEntry s off endWord rem n rest).halt = s.halt := rfl

@[simp] theorem firstEntry_fork (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) :
    (firstEntry s off endWord rem n rest).fork = s.fork := rfl

@[simp] theorem firstResult_executionEnv (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (firstResult s H off endWord rem n rest).executionEnv = s.executionEnv := rfl

@[simp] theorem firstResult_halt (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (firstResult s H off endWord rem n rest).halt = s.halt := rfl

@[simp] theorem firstResult_fork (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (firstResult s H off endWord rem n rest).fork = s.fork := rfl

@[simp] theorem firstResult_activeWords (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (firstResult s H off endWord rem n rest).activeWords = UInt256.ofNat 140 := rfl

@[simp] theorem cleared_executionEnv (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (cleared s H off endWord rem n rest).executionEnv = s.executionEnv := rfl

@[simp] theorem cleared_halt (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (cleared s H off endWord rem n rest).halt = s.halt := rfl

@[simp] theorem cleared_fork (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (cleared s H off endWord rem n rest).fork = s.fork := rfl

@[simp] theorem cleared_callStack (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (cleared s H off endWord rem n rest).callStack = s.callStack := rfl

@[simp] theorem cleared_activeWords (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (cleared s H off endWord rem n rest).activeWords = UInt256.ofNat 140 := rfl

@[simp] theorem lengthEntry_executionEnv (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) :
    (lengthEntry s off endWord rem n rest).executionEnv = s.executionEnv := rfl

@[simp] theorem lengthEntry_halt (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) :
    (lengthEntry s off endWord rem n rest).halt = s.halt := rfl

@[simp] theorem lengthEntry_fork (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) :
    (lengthEntry s off endWord rem n rest).fork = s.fork := rfl

@[simp] theorem finalResult_executionEnv (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (finalResult s H off endWord rem n rest).executionEnv = s.executionEnv := rfl

@[simp] theorem finalResult_halt (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (finalResult s H off endWord rem n rest).halt = s.halt := rfl

@[simp] theorem finalResult_fork (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (finalResult s H off endWord rem n rest).fork = s.fork := rfl

@[simp] theorem finalResult_activeWords (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (finalResult s H off endWord rem n rest).activeWords = UInt256.ofNat 140 := rfl

@[simp] theorem outputResult_callStack (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (outputResult s H off endWord rem n rest).callStack = s.callStack := rfl

@[simp] theorem outputResult_halt (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (outputResult s H off endWord rem n rest).halt = .Returned := rfl

@[simp] theorem outputResult_activeWords (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (outputResult s H off endWord rem n rest).activeWords = UInt256.ofNat 140 := rfl

theorem prepared_hash (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hrem : rem.toNat < 64)
    (hH : HashCorrect s.memory H) :
    HashCorrect (prepared s off endWord rem n rest).memory H := by
  intro i hi
  unfold prepared hValue hOffset
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  · rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
    · exact hH i hi
    · left
      omega
  · left
    have hadd : (UInt256.ofNat 288 + rem).toNat = 288 + rem.toNat := by
      rw [Challenge.EvmProof.Word.word_toNat_add,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
      norm_num
    rw [hadd]
    omega

theorem prepared_constants (s : State)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hrem : rem.toNat < 64)
    (hK : ConstantsCorrect s.memory) :
    ConstantsCorrect (prepared s off endWord rem n rest).memory := by
  intro i hi
  unfold prepared kValue kOffset
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  · rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
    · exact hK i hi
    · right
      rw [Challenge.EvmProof.Memory.readPadded_size]
      omega
  · right
    have hadd : (UInt256.ofNat 288 + rem).toNat = 288 + rem.toNat := by
      rw [Challenge.EvmProof.Word.word_toNat_add,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
      norm_num
    rw [hadd]
    change 288 + rem.toNat + 1 ≤ 2432 + i * 32
    omega

theorem writeStaging_hash (memory bytes : ByteArray) (start : Nat)
    (H : Array UInt32) (hstart : 288 ≤ start)
    (hH : HashCorrect memory H) :
    HashCorrect (MachineState.writeBytes memory bytes start) H := by
  intro i hi
  unfold hValue hOffset
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  · exact hH i hi
  · left
    omega

theorem writeStaging_constants (memory bytes : ByteArray) (start : Nat)
    (hend : start + bytes.size ≤ 2432)
    (hK : ConstantsCorrect memory) :
    ConstantsCorrect (MachineState.writeBytes memory bytes start) := by
  intro i hi
  unfold kValue kOffset
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  · exact hK i hi
  · right
    omega

def firstHash (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) : Array UInt32 :=
  Sha256.compressBlock H (prepared s off endWord rem n rest).memory 288

theorem firstResult_hash (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    HashCorrect (firstResult s H off endWord rem n rest).memory
      (firstHash s H off endWord rem n rest) := by
  simpa [firstResult, firstHash, firstEntry, longBranch] using
    CompressionCorrect.finalState_hash
      (firstEntry s off endWord rem n rest) H (UInt256.ofNat 2522)
      ([off, endWord, rem, n] ++ rest)

theorem firstResult_constants (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hK : ConstantsCorrect (prepared s off endWord rem n rest).memory) :
    ConstantsCorrect (firstResult s H off endWord rem n rest).memory := by
  apply CompressionCorrect.finalState_constants
  simpa [firstEntry, longBranch] using hK

theorem cleared_hash (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    HashCorrect (cleared s H off endWord rem n rest).memory
      (firstHash s H off endWord rem n rest) := by
  unfold cleared
  apply writeStaging_hash
  · omega
  · apply writeStaging_hash
    · omega
    · exact firstResult_hash s H off endWord rem n rest

theorem cleared_constants (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hK : ConstantsCorrect (prepared s off endWord rem n rest).memory) :
    ConstantsCorrect (cleared s H off endWord rem n rest).memory := by
  unfold cleared
  apply writeStaging_constants
  · simp
  · apply writeStaging_constants
    · simp
    · exact firstResult_constants s H off endWord rem n rest hK

theorem lengthEntry_hash (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hH : HashCorrect s.memory H) :
    HashCorrect (lengthEntry s off endWord rem n rest).memory H := by
  unfold lengthEntry
  apply writeStaging_hash
  · omega
  · exact hH

theorem lengthEntry_constants (s : State)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hK : ConstantsCorrect s.memory) :
    ConstantsCorrect (lengthEntry s off endWord rem n rest).memory := by
  unfold lengthEntry
  apply writeStaging_constants
  · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  · exact hK

theorem finalResult_hash (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    HashCorrect (finalResult s H off endWord rem n rest).memory
      (finalHash s H off endWord rem n rest) := by
  simpa [finalResult, finalHash] using CompressionCorrect.finalState_hash
    (lengthEntry s off endWord rem n rest) H (UInt256.ofNat 2562)
    ([off, endWord, rem, n] ++ rest)

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailState
