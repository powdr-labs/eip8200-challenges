import Challenge.Bls12381G2Add.Reference.Proofs.SourcePointStoresDefs
import YulEvmCompiler.Optimizer.Implementation.MemorySpillStateSound

set_option warningAsError true

/-! # Staged memory boundary for the frozen G2ADD point copy helper -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

private theorem copyPointState0_loadWord_high (yst : EvmState)
    (point : U256) (offset : Nat) (hoff : 256 ≤ offset) :
    loadWord (copyPointState0 yst point).memory offset =
      loadWord yst.memory offset := by
  rw [copyPointState0_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
  omega

private theorem copyPointState1_loadWord_high (yst : EvmState)
    (point : U256) (offset : Nat) (hoff : 256 ≤ offset) :
    loadWord (copyPointState1 yst point).memory offset =
      loadWord yst.memory offset := by
  rw [copyPointState1_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
  · exact copyPointState0_loadWord_high yst point offset hoff
  · omega

private theorem copyPointState2_loadWord_high (yst : EvmState)
    (point : U256) (offset : Nat) (hoff : 256 ≤ offset) :
    loadWord (copyPointState2 yst point).memory offset =
      loadWord yst.memory offset := by
  rw [copyPointState2_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
  · exact copyPointState1_loadWord_high yst point offset hoff
  · omega

private theorem copyPointState3_loadWord_high (yst : EvmState)
    (point : U256) (offset : Nat) (hoff : 256 ≤ offset) :
    loadWord (copyPointState3 yst point).memory offset =
      loadWord yst.memory offset := by
  rw [copyPointState3_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
  · exact copyPointState2_loadWord_high yst point offset hoff
  · omega

private theorem copyPointState4_loadWord_high (yst : EvmState)
    (point : U256) (offset : Nat) (hoff : 256 ≤ offset) :
    loadWord (copyPointState4 yst point).memory offset =
      loadWord yst.memory offset := by
  rw [copyPointState4_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
  · exact copyPointState3_loadWord_high yst point offset hoff
  · omega

private theorem copyPointState5_loadWord_high (yst : EvmState)
    (point : U256) (offset : Nat) (hoff : 256 ≤ offset) :
    loadWord (copyPointState5 yst point).memory offset =
      loadWord yst.memory offset := by
  rw [copyPointState5_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
  · exact copyPointState4_loadWord_high yst point offset hoff
  · omega

private theorem copyPointState6_loadWord_high (yst : EvmState)
    (point : U256) (offset : Nat) (hoff : 256 ≤ offset) :
    loadWord (copyPointState6 yst point).memory offset =
      loadWord yst.memory offset := by
  rw [copyPointState6_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
  · exact copyPointState5_loadWord_high yst point offset hoff
  · omega

private theorem copyPointState_loadWord_high (yst : EvmState)
    (point : U256) (offset : Nat) (hoff : 256 ≤ offset) :
    loadWord (copyPointState yst point).memory offset =
      loadWord yst.memory offset := by
  rw [copyPointState_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
  · exact copyPointState6_loadWord_high yst point offset hoff
  · omega

theorem copyPointState_256_word0 (yst : EvmState) :
    loadWord (copyPointState yst 256).memory 0 =
      loadWord yst.memory 256 := by
  rw [copyPointState_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState6_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState5_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState4_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState3_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState2_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState1_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState0_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord]
  congr 1

theorem copyPointState_256_word1 (yst : EvmState) :
    loadWord (copyPointState yst 256).memory 32 =
      loadWord yst.memory 288 := by
  rw [copyPointState_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState6_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState5_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState4_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState3_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState2_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState1_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord,
    copyPointState0_loadWord_high _ _ _ (by decide)]
  congr 1

theorem copyPointState_256_word2 (yst : EvmState) :
    loadWord (copyPointState yst 256).memory 64 =
      loadWord yst.memory 320 := by
  rw [copyPointState_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState6_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState5_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState4_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState3_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState2_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord,
    copyPointState1_loadWord_high _ _ _ (by decide)]
  congr 1

theorem copyPointState_256_word3 (yst : EvmState) :
    loadWord (copyPointState yst 256).memory 96 =
      loadWord yst.memory 352 := by
  rw [copyPointState_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState6_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState5_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState4_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState3_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord,
    copyPointState2_loadWord_high _ _ _ (by decide)]
  congr 1

theorem copyPointState_256_word4 (yst : EvmState) :
    loadWord (copyPointState yst 256).memory 128 =
      loadWord yst.memory 384 := by
  rw [copyPointState_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState6_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState5_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState4_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord,
    copyPointState3_loadWord_high _ _ _ (by decide)]
  congr 1

theorem copyPointState_256_word5 (yst : EvmState) :
    loadWord (copyPointState yst 256).memory 160 =
      loadWord yst.memory 416 := by
  rw [copyPointState_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState6_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState5_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord,
    copyPointState4_loadWord_high _ _ _ (by decide)]
  congr 1

theorem copyPointState_256_word6 (yst : EvmState) :
    loadWord (copyPointState yst 256).memory 192 =
      loadWord yst.memory 448 := by
  rw [copyPointState_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ _ _ _ (by omega), copyPointState6_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord,
    copyPointState5_loadWord_high _ _ _ (by decide)]
  congr 1

theorem copyPointState_256_word7 (yst : EvmState) :
    loadWord (copyPointState yst 256).memory 224 =
      loadWord yst.memory 480 := by
  rw [copyPointState_memory,
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord,
    copyPointState6_loadWord_high _ _ _ (by decide)]
  congr 1

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
