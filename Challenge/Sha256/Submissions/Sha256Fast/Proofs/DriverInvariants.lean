import Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverCorrect

set_option warningAsError true

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverInvariants

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open MemoryCorrect DriverCorrect

theorem blockResult_hash (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    HashCorrect (blockResult s H off endWord rem n rest).memory
      (Sha256.compressBlock H s.executionEnv.calldata off.toNat) := by
  have h := CompressionCorrect.finalState_hash
    (copiedState s off endWord rem n rest) H (UInt256.ofNat 2480)
    ([off, endWord, rem, n] ++ rest)
  change HashCorrect _
    (Sha256.compressBlock H
      (MachineState.writeBytes s.memory
        (MachineState.readPadded s.executionEnv.calldata off.toNat 64) 288) 288) at h
  rw [BlockBridge.compressBlock_stagedCalldata H s.memory
    s.executionEnv.calldata off.toNat] at h
  simpa [blockResult] using h

theorem blockResult_constants (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hK : ConstantsCorrect s.memory) :
    ConstantsCorrect (blockResult s H off endWord rem n rest).memory := by
  apply CompressionCorrect.finalState_constants
  exact copied_constants s off endWord rem n rest hK

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverInvariants
