import Challenge.Bls12381G2Add.Reference.Proofs.SourceInputCodec
import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainPointDefs
import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveLowMemory
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddPreservation

set_option warningAsError true

/-! # Low-memory preservation across G2ADD point validation -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

private theorem onCurveStateAfterConstant_loadWord_low (yst : EvmState)
    (x y : U256) (offset : Nat) (hend : offset + 32 ≤ 1024) :
    loadWord (onCurveStateAfterConstant yst x y).memory offset =
      loadWord (onCurveStateAfterX3 yst x y).memory offset := by
  unfold onCurveStateAfterConstant
  change loadWord
    (storeWord (storeWord (storeWord (storeWord _ 2432 0) 2464 4) 2496 0)
      2528 4) offset = _
  rw [loadWord_storeWord_disjoint _ 2528 offset _ (by omega),
    loadWord_storeWord_disjoint _ 2496 offset _ (by omega),
    loadWord_storeWord_disjoint _ 2464 offset _ (by omega),
    loadWord_storeWord_disjoint _ 2432 offset _ (by omega)]

theorem onCurveFinalState_loadWord_low (yst : EvmState) (x y : U256)
    (offset : Nat) (hend : offset + 32 ≤ 1024) :
    loadWord (onCurveFinalState yst x y).memory offset =
      loadWord yst.memory offset := by
  rw [show (onCurveFinalState yst x y).memory =
      (onCurveStateAfterAdd yst x y).memory by rfl]
  unfold onCurveStateAfterAdd
  rw [fp2AddContractState_loadWord_before_out _ _ _ _ (by norm_num)
      offset (by norm_num; omega),
    onCurveStateAfterConstant_loadWord_low yst x y offset hend]
  unfold onCurveStateAfterX3
  rw [fp2MulFinalState_loadWord_before_scratch _ _ _ _ offset hend
    (by norm_num) (by norm_num)]
  unfold onCurveStateAfterX2
  rw [fp2MulFinalState_loadWord_before_scratch _ _ _ _ offset hend
    (by norm_num) (by norm_num)]
  unfold onCurveStateAfterY2
  exact fp2MulFinalState_loadWord_before_scratch _ _ _ _ offset hend
    (by norm_num) (by norm_num)

theorem mainAfterInf1Reads_memory (yst : EvmState) :
    (mainAfterInf1Reads yst).memory = (mainDecodedState yst).memory := by
  rfl

theorem mainAfterInf2Reads_memory (yst : EvmState) :
    (mainAfterInf2Reads yst).memory = (mainDecodedState yst).memory := by
  rfl

theorem mainAfterCurve1_loadWord_low (yst : EvmState) (offset : Nat)
    (hend : offset + 32 ≤ 1024) :
    loadWord (mainAfterCurve1 yst).memory offset =
      mainDecodedWord yst offset := by
  unfold mainAfterCurve1
  rw [onCurveFinalState_loadWord_low _ _ _ offset hend,
    mainAfterInf2Reads_memory]
  rfl

theorem mainValidatedState_loadWord_low (yst : EvmState) (offset : Nat)
    (hend : offset + 32 ≤ 1024) :
    loadWord (mainValidatedState yst).memory offset =
      mainDecodedWord yst offset := by
  unfold mainValidatedState
  rw [onCurveFinalState_loadWord_low _ _ _ offset hend,
    mainAfterCurve1_loadWord_low yst offset hend]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
