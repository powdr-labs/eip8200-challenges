import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulRefinement

set_option warningAsError true

/-! # Native multiplication memory locality -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

/-- Native multiplication has no EVM-state effects, hence preserves every
byte range below the historical scratch bound. -/
theorem fpMulFinalState_readBytes_before_scratch (yst : EvmState)
    (ahi alo bhi blo : U256) (start size : Nat)
    (_hend : start + size ≤ 1024) :
    readBytes (fpMulFinalState yst ahi alo bhi blo).memory start size =
      readBytes yst.memory start size := by
  rfl

theorem fpMulFinalState_loadWord_before_scratch (yst : EvmState)
    (ahi alo bhi blo : U256) (offset : Nat)
    (_hend : offset + 32 ≤ 1024) :
    loadWord (fpMulFinalState yst ahi alo bhi blo).memory offset =
      loadWord yst.memory offset := by
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
