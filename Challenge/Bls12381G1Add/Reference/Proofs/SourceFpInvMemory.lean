import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvRefinement

set_option warningAsError true

/-! # Frozen G1ADD inversion scratch-memory boundary -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

/-- The fixed inversion scratch region starts at byte 1024, so every decoded
input word below it is preserved. -/
theorem fpInvFinalState_loadWord_before_scratch (yst : EvmState)
    (hi lo : U256) (offset : Nat) (hend : offset + 32 ≤ 1024) :
    loadWord (fpInvFinalState yst hi lo).memory offset =
      loadWord yst.memory offset := by
  unfold loadWord
  have hbyte : ∀ i, i < 32 →
      (fpInvFinalState yst hi lo).memory (offset + i) =
        yst.memory (offset + i) := by
    intro i hiLt
    simp only [fpInvFinalState, fpInvCallState, fpInvResponse, finishCall,
      fpInvInputState_memory, touchMemory, copyReturn, storeWord]
    repeat' rw [if_neg]
    all_goals omega
  have hfold : ∀ (indices : List Nat),
      (∀ i ∈ indices, i < 32) → ∀ acc : BitVec 256,
      indices.foldl (fun (word : BitVec 256) (i : Nat) =>
          (word <<< (8 : Nat)) |||
          BitVec.ofNat 256
            ((fpInvFinalState yst hi lo).memory (offset + i)).toNat) acc =
        indices.foldl (fun (word : BitVec 256) (i : Nat) =>
          (word <<< (8 : Nat)) |||
          BitVec.ofNat 256 (yst.memory (offset + i)).toNat) acc := by
    intro indices hindices acc
    induction indices generalizing acc with
    | nil => rfl
    | cons i rest ih =>
        rw [List.foldl_cons, List.foldl_cons, hbyte i (hindices i (by simp))]
        apply ih
        intro j hj
        exact hindices j (by simp [hj])
  exact hfold (List.range 32) (by simp) 0

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
