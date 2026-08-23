import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFinitePostLawful
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvMemory

set_option warningAsError true

/-! # G1ADD finite slope-state memory preservation -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem mainFiniteDoubleFinalState_loadWord (yst : EvmState) (offset : Nat)
    (hend : offset + 32 ≤ 1024) :
    loadWord (mainFiniteDoubleFinalState yst).memory offset =
      mainDecodedWord yst offset := by
  rw [mainFiniteDoubleFinalState,
    fpMulFinalState_loadWord_before_scratch _ _ _ _ _ _ hend]
  rw [mainFiniteDoubleState2,
    fpInvFinalState_loadWord_before_scratch _ _ _ _ hend]
  rw [mainFiniteDoubleDenArgsState, afterFourLoads_memory]
  rw [mainFiniteDoubleState1,
    fpMulFinalState_loadWord_before_scratch _ _ _ _ _ _ hend]
  rw [mainFiniteDoubleXSqArgsState, afterFourLoads_memory]
  exact mainFiniteYZeroArgsState_loadWord yst offset hend

private theorem unequalState1_loadWord (yst : EvmState) (offset : Nat)
    (hend : offset + 32 ≤ 1024) :
    loadWord (mainFiniteUnequalState1 yst).memory offset =
      mainDecodedWord yst offset := by
  rw [mainFiniteUnequalState1,
    fpInvFinalState_loadWord_before_scratch _ _ _ _ hend]
  exact mainFiniteUnequalDenominatorArgsState_loadWord yst offset hend

theorem mainFiniteUnequalFinalState_loadWord (yst : EvmState) (offset : Nat)
    (hend : offset + 32 ≤ 1024) :
    loadWord (mainFiniteUnequalFinalState yst).memory offset =
      mainDecodedWord yst offset := by
  rw [mainFiniteUnequalFinalState,
    fpMulFinalState_loadWord_before_scratch _ _ _ _ _ _ hend]
  exact unequalState1_loadWord yst offset hend

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
