import Challenge.Sha256.Submissions.Sha256Fast.Proofs.InitializationMemory
import Challenge.Sha256.Submissions.Sha256Fast.Proofs.BlockBridge

set_option warningAsError true

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverCorrect

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof
open MemoryCorrect

def copiedState (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 4
    activeWords := UInt256.ofNat 140
    memory := MachineState.writeBytes s.memory
      (MachineState.readPadded s.executionEnv.calldata off.toNat 64) 288
    stack := [UInt256.ofNat 2480, off, endWord, rem, n] ++ rest }

def blockResult (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) : State :=
  CompressionCorrect.finalState
    (copiedState s off endWord rem n rest) H (UInt256.ofNat 2480)
    ([off, endWord, rem, n] ++ rest)

theorem copied_hash (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hH : HashCorrect s.memory H) :
    HashCorrect (copiedState s off endWord rem n rest).memory H := by
  intro i hi
  unfold copiedState hValue hOffset
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  · exact hH i hi
  · left
    omega

theorem copied_constants (s : State)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hK : ConstantsCorrect s.memory) :
    ConstantsCorrect (copiedState s off endWord rem n rest).memory := by
  intro i hi
  unfold copiedState kValue kOffset
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  · exact hK i hi
  · right
    rw [Challenge.EvmProof.Memory.readPadded_size]
    omega

def testedState (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) : State :=
  let b := blockResult s H off endWord rem n rest
  { b with
    pc := UInt256.ofNat 2490
    stack := [UInt256.ofNat 2465,
      UInt256.lt (UInt256.ofNat 64 + off) endWord,
      UInt256.ofNat 64 + off, endWord, rem, n] ++ rest }

def nextFullState (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) : State :=
  { testedState s H off endWord rem n rest with
    pc := UInt256.ofNat 2465
    stack := [UInt256.ofNat 64 + off, endWord, rem, n] ++ rest }

def tailState (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) : State :=
  { testedState s H off endWord rem n rest with
    pc := UInt256.ofNat 2491
    stack := [UInt256.ofNat 64 + off, endWord, rem, n] ++ rest }

@[simp] theorem blockResult_executionEnv (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (blockResult s H off endWord rem n rest).executionEnv = s.executionEnv := rfl

@[simp] theorem blockResult_halt (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (blockResult s H off endWord rem n rest).halt = s.halt := rfl

@[simp] theorem blockResult_fork (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (blockResult s H off endWord rem n rest).fork = s.fork := rfl

@[simp] theorem nextFullState_executionEnv (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (nextFullState s H off endWord rem n rest).executionEnv = s.executionEnv := rfl

@[simp] theorem nextFullState_halt (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (nextFullState s H off endWord rem n rest).halt = s.halt := rfl

@[simp] theorem nextFullState_fork (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (nextFullState s H off endWord rem n rest).fork = s.fork := rfl

@[simp] theorem nextFullState_callStack (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (nextFullState s H off endWord rem n rest).callStack = s.callStack := rfl

@[simp] theorem tailState_executionEnv (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (tailState s H off endWord rem n rest).executionEnv = s.executionEnv := rfl

@[simp] theorem tailState_halt (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (tailState s H off endWord rem n rest).halt = s.halt := rfl

@[simp] theorem tailState_fork (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (tailState s H off endWord rem n rest).fork = s.fork := rfl

@[simp] theorem tailState_callStack (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (tailState s H off endWord rem n rest).callStack = s.callStack := rfl

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverCorrect
