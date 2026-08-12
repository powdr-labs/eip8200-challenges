import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulRefinement
import Challenge.EvmProof.CallMemory
import Challenge.EvmProof.ModexpMemory

set_option warningAsError true

/-! # Frozen G1ADD multiplication scratch-memory locality -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

/-- The frozen multiplication helper writes only at its MODEXP scratch region,
so every byte range wholly below offset 1024 is preserved. -/
theorem fpMulFinalState_readBytes_before_scratch (yst : EvmState)
    (ahi alo bhi blo : U256) (start size : Nat)
    (hend : start + size ≤ 1024) :
    readBytes (fpMulFinalState yst ahi alo bhi blo).memory start size =
      readBytes yst.memory start size := by
  rw [show (fpMulFinalState yst ahi alo bhi blo).memory =
      copyReturn (fpMulInputState yst ahi alo bhi blo).memory 1280 48
        (fpMulResponse yst ahi alo bhi blo).returndata by rfl]
  rw [Challenge.EvmProof.readBytes_copyReturn_disjoint]
  · rw [fpMulInputState_memory]
    repeat' rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint]
    rw [Challenge.EvmProof.ModexpMemory.readBytes_storeByte_disjoint]
    repeat' rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint]
    all_goals omega
  · left
    omega

theorem fpMulFinalState_loadWord_before_scratch (yst : EvmState)
    (ahi alo bhi blo : U256) (offset : Nat)
    (hend : offset + 32 ≤ 1024) :
    loadWord (fpMulFinalState yst ahi alo bhi blo).memory offset =
      loadWord yst.memory offset := by
  unfold loadWord
  have hbyte (i : Nat) (hi : i < 32) :
      (fpMulFinalState yst ahi alo bhi blo).memory (offset + i) =
        yst.memory (offset + i) := by
    have hread := fpMulFinalState_readBytes_before_scratch yst ahi alo bhi blo
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

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
