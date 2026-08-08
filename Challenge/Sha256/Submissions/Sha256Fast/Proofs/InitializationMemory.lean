import Challenge.Sha256.Submissions.Sha256Fast.Proofs.InitializationCorrect

set_option warningAsError true

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.InitializationMemory

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open MemoryCorrect
open InitializationCorrect

theorem c0_memory (s : State) (n : UInt256) :
    (c0 s n).memory =
      DriverBlocks.constantMemory0 (DriverBlocks.hashMemory s.memory) := by
  rfl

theorem c1_memory (s : State) (n : UInt256) :
    (c1 s n).memory = DriverBlocks.constantMemory1
      (DriverBlocks.constantMemory0 (DriverBlocks.hashMemory s.memory)) := by
  rw [c1]
  change DriverBlocks.constantMemory1 (c0 s n).memory = _
  rw [c0_memory]

theorem c2_memory (s : State) (n : UInt256) :
    (c2 s n).memory = DriverBlocks.constantMemory2 (c1 s n).memory := by rfl

theorem c3_memory (s : State) (n : UInt256) :
    (c3 s n).memory = DriverBlocks.constantMemory3 (c2 s n).memory := by rfl

theorem c4_memory (s : State) (n : UInt256) :
    (c4 s n).memory = DriverBlocks.constantMemory4 (c3 s n).memory := by rfl

theorem c5_memory (s : State) (n : UInt256) :
    (c5 s n).memory = DriverBlocks.constantMemory5 (c4 s n).memory := by rfl

theorem c6_memory (s : State) (n : UInt256) :
    (c6 s n).memory = DriverBlocks.constantMemory6 (c5 s n).memory := by rfl

theorem c7_memory (s : State) (n : UInt256) :
    (c7 s n).memory = DriverBlocks.constantMemory7 (c6 s n).memory := by rfl

theorem finalState_memory (s : State) (n : UInt256) :
    (finalState s n).memory = DriverBlocks.initializedMemory s.memory := by
  rw [show (finalState s n).memory = (c7 s n).memory by rfl,
    c7_memory, c6_memory, c5_memory, c4_memory, c3_memory, c2_memory,
    c1_memory]
  rfl

theorem finalState_hash (s : State) (n : UInt256) :
    HashCorrect (finalState s n).memory Sha256.H0 := by
  rw [finalState_memory]
  exact MemoryCorrect.initialized_hash s.memory

theorem finalState_constants (s : State) (n : UInt256) :
    ConstantsCorrect (finalState s n).memory := by
  rw [finalState_memory]
  exact MemoryCorrect.initialized_constants s.memory

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.InitializationMemory
