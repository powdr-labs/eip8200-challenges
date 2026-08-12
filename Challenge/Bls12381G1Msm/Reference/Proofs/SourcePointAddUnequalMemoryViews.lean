import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalFinalReadback

set_option warningAsError true

/-! Stable high-memory views during unequal affine addition. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem pointAddUnequalX3State_loadWord_after_scratch (yst : EvmState)
    (out left right : U256) (offset : Nat) (hstart : 1328 ≤ offset) :
    loadWord (pointAddUnequalX3State yst out left right).memory offset =
      loadWord (pointAddPrefixState yst out left right).memory offset := by
  rw [pointAddUnequalX3State,
    fpMulFinalState_loadWord_after_scratch _ _ _ _ _ offset hstart,
    pointAddUnequalLambdaState,
    fpMulFinalState_loadWord_after_scratch _ _ _ _ _ offset hstart,
    pointAddUnequalInvFinalState,
    fpInvFinalState_loadWord_after_scratch _ _ _ offset hstart,
    pointAddUnequalNumeratorInputsState_memory_eq_prefix]

@[simp] theorem pointAddUnequalXSubLeftPtr_eq (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalXSubLeftPtr yst out left right = left := by
  rw [pointAddUnequalXSubLeftPtr,
    pointAddUnequalX3State_loadWord_after_scratch _ _ _ _ 1568 (by omega)]
  simp only [pointAddPrefixState, pointAddStore]
  rw [YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
      _ 1600 1568 _ (by omega),
    YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord]

@[simp] theorem pointAddUnequalXSubRightPtr_eq (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalXSubRightPtr
      (pointAddUnequalXSubRightContext yst out left right) = right := by
  rw [pointAddUnequalXSubRightPtr]
  change loadWord
    (pointAddUnequalXSubLeftRawState yst out left right).memory 1600 = right
  rw [pointAddUnequalXSubLeftRawState_memory,
    pointAddUnequalX3State_loadWord_after_scratch _ _ _ _ 1600 (by omega)]
  simp only [pointAddPrefixState, pointAddStore]
  rw [YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
