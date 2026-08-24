import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvResultDefs

set_option warningAsError true

/-! # Native G1ADD inversion memory frame -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

/-- Native stack-only inversion preserves every memory word.  The legacy
scratch-bound premise remains for downstream compatibility. -/
theorem fpInvFinalState_loadWord_before_scratch (yst : EvmState)
    (hi lo : U256) (offset : Nat) (_hend : offset + 32 ≤ 1024) :
    loadWord (fpInvFinalState yst hi lo).memory offset =
      loadWord yst.memory offset := by
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
