import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpMulExec
import Challenge.EvmProof.CallMemory
import Challenge.EvmProof.ModexpMemory
import YulEvmCompiler.Optimizer.Implementation.MemorySpillStateSound

set_option warningAsError true

/-! # Frozen G2ADD multiplication scratch-memory locality

The scalar `fpMul` helper uses `[1024, 1328)` as private MODEXP scratch.
These lemmas expose the high-memory side of that boundary.  Keeping this
fact opaque prevents every Fp2 phase from normalizing the complete MODEXP
input and call-return state graph.
-/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem loadWord_storeWord_same (memory : Nat → UInt8) (slot : Nat)
    (value : U256) :
    loadWord (storeWord memory slot value) slot = value :=
  YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord
    memory slot value

theorem loadWord_storeWord_disjoint (memory : Nat → UInt8)
    (writtenSlot untouchedSlot : Nat) (value : U256)
    (hdisjoint : writtenSlot + 32 ≤ untouchedSlot ∨
      untouchedSlot + 32 ≤ writtenSlot) :
    loadWord (storeWord memory writtenSlot value) untouchedSlot =
      loadWord memory untouchedSlot :=
  YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
    memory writtenSlot untouchedSlot value hdisjoint

theorem fpMulFinalState_readBytes_after_scratch (yst : EvmState)
    (ahi alo bhi blo : U256) (start size : Nat)
    (hstart : 1328 ≤ start) :
    readBytes (fpMulFinalState yst ahi alo bhi blo).memory start size =
      readBytes yst.memory start size := by
  rw [show (fpMulFinalState yst ahi alo bhi blo).memory =
      copyReturn (fpMulInputState yst ahi alo bhi blo).memory 1280 48
        (fpMulResponse yst ahi alo bhi blo).returndata by rfl]
  rw [Challenge.EvmProof.readBytes_copyReturn_disjoint]
  · rw [Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulInputState_memory]
    repeat' rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint]
    rw [Challenge.EvmProof.ModexpMemory.readBytes_storeByte_disjoint]
    repeat' rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint]
    all_goals omega
  · right
    omega

theorem fpMulFinalState_loadWord_after_scratch (yst : EvmState)
    (ahi alo bhi blo : U256) (offset : Nat) (hstart : 1328 ≤ offset) :
    loadWord (fpMulFinalState yst ahi alo bhi blo).memory offset =
      loadWord yst.memory offset := by
  unfold loadWord
  have hbyte (i : Nat) (hi : i < 32) :
      (fpMulFinalState yst ahi alo bhi blo).memory (offset + i) =
        yst.memory (offset + i) := by
    have hread := fpMulFinalState_readBytes_after_scratch yst ahi alo bhi blo
      (offset + i) 1 (by omega)
    simpa [readBytes] using hread
  have hfold : ∀ (indices : List Nat) (acc : U256),
      (∀ i ∈ indices, i < 32) →
      indices.foldl (fun (acc : U256) (i : Nat) =>
          (acc <<< (8 : Nat)) |||
            BitVec.ofNat 256
              ((fpMulFinalState yst ahi alo bhi blo).memory
                (offset + i)).toNat) acc =
        indices.foldl (fun (acc : U256) (i : Nat) =>
          (acc <<< (8 : Nat)) |||
            BitVec.ofNat 256 (yst.memory (offset + i)).toNat) acc := by
    intro indices
    induction indices with
    | nil => simp
    | cons i rest ih =>
      intro acc hall
      rw [List.foldl_cons, List.foldl_cons, hbyte i (hall i (by simp))]
      exact ih _ (fun j hj => hall j (by simp [hj]))
  exact hfold (List.range 32) 0 (by
    intro i hi
    simpa using hi)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
