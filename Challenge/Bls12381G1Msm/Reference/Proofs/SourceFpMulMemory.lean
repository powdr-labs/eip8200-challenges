import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulExec
import Challenge.EvmProof.CallMemory
import Challenge.EvmProof.ModexpMemory

set_option warningAsError true

/-! The scalar `fpMul` helper only mutates its private `[1024,1328)` scratch. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fpMulFinalState_readBytes_after_scratch (yst : EvmState)
    (ahi alo bhi blo : U256) (start size : Nat)
    (hstart : 1328 ≤ start) :
    readBytes (fpMulFinalState yst ahi alo bhi blo).memory start size =
      readBytes yst.memory start size := by
  rw [show (fpMulFinalState yst ahi alo bhi blo).memory =
      copyReturn (fpMulInputState yst ahi alo bhi blo).memory 1280 48
        (fpMulResponse yst ahi alo bhi blo).returndata by rfl]
  rw [Challenge.EvmProof.readBytes_copyReturn_disjoint]
  · rw [show (fpMulInputState yst ahi alo bhi blo).memory =
        (Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulInputState
          yst ahi alo bhi blo).memory by rfl]
    rw [Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulInputState_memory]
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

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
