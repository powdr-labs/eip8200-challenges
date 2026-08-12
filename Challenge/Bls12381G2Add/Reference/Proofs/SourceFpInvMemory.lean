import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpInvExec
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvMemory
import Challenge.EvmProof.CallMemory
import Challenge.EvmProof.ModexpMemory

set_option warningAsError true

/-! # Frozen G2ADD inversion scratch-memory locality

The scalar `fpInv` helper writes only inside `[1024, 1328)`.  These opaque
lemmas let Fp2 inversion preserve its operands and scratch results without
re-elaborating the MODEXP input and return-copy graph.
-/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

/-- The scalar inversion helper's fixed scratch region starts at byte 1024,
so decoded point words below it are preserved. -/
theorem fpInvFinalState_loadWord_before_scratch (yst : EvmState)
    (hi lo : U256) (offset : Nat) (hend : offset + 32 ≤ 1024) :
    loadWord (fpInvFinalState yst hi lo).memory offset =
      loadWord yst.memory offset := by
  exact Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvFinalState_loadWord_before_scratch
    yst hi lo offset hend

theorem fpInvFinalState_readBytes_after_scratch (yst : EvmState)
    (hi lo : U256) (start size : Nat) (hstart : 1328 ≤ start) :
    readBytes (fpInvFinalState yst hi lo).memory start size =
      readBytes yst.memory start size := by
  rw [show (fpInvFinalState yst hi lo).memory =
      copyReturn (fpInvInputState yst hi lo).memory 1280 48
        (fpInvResponse yst hi lo).returndata by rfl]
  rw [Challenge.EvmProof.readBytes_copyReturn_disjoint]
  · rw [Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvInputState_memory]
    repeat' rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint]
    all_goals omega
  · right
    omega

theorem fpInvFinalState_loadWord_after_scratch (yst : EvmState)
    (hi lo : U256) (offset : Nat) (hstart : 1328 ≤ offset) :
    loadWord (fpInvFinalState yst hi lo).memory offset =
      loadWord yst.memory offset := by
  unfold loadWord
  have hbyte (i : Nat) (hi' : i < 32) :
      (fpInvFinalState yst hi lo).memory (offset + i) =
        yst.memory (offset + i) := by
    have hread := fpInvFinalState_readBytes_after_scratch yst hi lo
      (offset + i) 1 (by omega)
    simpa [readBytes] using hread
  have hfold : ∀ (indices : List Nat) (acc : U256),
      (∀ i ∈ indices, i < 32) →
      indices.foldl (fun (acc : U256) (i : Nat) =>
          (acc <<< (8 : Nat)) |||
            BitVec.ofNat 256
              ((fpInvFinalState yst hi lo).memory (offset + i)).toNat) acc =
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
    intro i hi'
    simpa using hi')

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
