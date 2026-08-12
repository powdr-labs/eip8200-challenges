import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvRefinement
import Challenge.EvmProof.CallMemory
import Challenge.EvmProof.ModexpMemory

set_option warningAsError true

/-! The shared inversion helper only mutates its private `[1024,1328)` scratch. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fpInvFinalState_readBytes_after_scratch (yst : EvmState)
    (hi lo : U256) (start size : Nat) (hstart : 1328 ≤ start) :
    readBytes
      (Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvFinalState
        yst hi lo).memory start size =
      readBytes yst.memory start size := by
  rw [show
      (Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvFinalState
        yst hi lo).memory =
      copyReturn
        (Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvInputState
          yst hi lo).memory 1280 48
        (Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvResponse
          yst hi lo).returndata by rfl]
  rw [Challenge.EvmProof.readBytes_copyReturn_disjoint]
  · rw [Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvInputState_memory]
    rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ start size 1232 _ (by omega)]
    rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ start size 1216 _ (by omega)]
    rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ start size 1184 _ (by omega)]
    rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ start size 1168 _ (by omega)]
    rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ start size 1136 _ (by omega)]
    rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ start size 1120 _ (by omega)]
    rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ start size 1088 _ (by omega)]
    rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ start size 1056 _ (by omega)]
    rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ start size 1024 _ (by omega)]
  · right
    omega

theorem fpInvFinalState_loadWord_after_scratch (yst : EvmState)
    (hi lo : U256) (offset : Nat) (hstart : 1328 ≤ offset) :
    loadWord
      (Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvFinalState
        yst hi lo).memory offset =
      loadWord yst.memory offset := by
  unfold loadWord
  have hbyte (i : Nat) (hiLt : i < 32) :
      (Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvFinalState
        yst hi lo).memory (offset + i) =
        yst.memory (offset + i) := by
    have hread := fpInvFinalState_readBytes_after_scratch yst hi lo
      (offset + i) 1 (by omega)
    simpa [readBytes] using hread
  have hfold : ∀ (indices : List Nat) (acc : U256),
      (∀ i ∈ indices, i < 32) →
      indices.foldl (fun (acc : U256) (i : Nat) =>
          (acc <<< (8 : Nat)) |||
            BitVec.ofNat 256
              ((Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvFinalState
                yst hi lo).memory
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
    intro i hiLt
    simpa using hiLt)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
