import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveHighPreservation

set_option warningAsError true

/-! # Preservation of `y²` through frozen G2ADD `onCurve` intermediates -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

private theorem onCurveX2_y2 (yst : EvmState) (x y : U256) :
    fp2At (onCurveStateAfterX2 yst x y) (BitVec.ofNat 256 2048) =
      fp2At (onCurveStateAfterY2 yst y) (BitVec.ofNat 256 2048) := by
  exact fp2MulFinalState_fp2At_before_out_high
    (onCurveStateAfterY2 yst y) (BitVec.ofNat 256 2176) x x
    (BitVec.ofNat 256 2048) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

private theorem onCurveX3_y2 (yst : EvmState) (x y : U256) :
    fp2At (onCurveStateAfterX3 yst x y) (BitVec.ofNat 256 2048) =
      fp2At (onCurveStateAfterY2 yst y) (BitVec.ofNat 256 2048) := by
  rw [onCurveStateAfterX3,
    fp2MulFinalState_fp2At_before_out_high
      (onCurveStateAfterX2 yst x y) (BitVec.ofNat 256 2304)
      (BitVec.ofNat 256 2176) x (BitVec.ofNat 256 2048)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    onCurveX2_y2]

theorem onCurveConstant_y2 (yst : EvmState) (x y : U256) :
    fp2At (onCurveStateAfterConstant yst x y) (BitVec.ofNat 256 2048) =
      fp2At (onCurveStateAfterY2 yst y) (BitVec.ofNat 256 2048) := by
  rw [← onCurveX3_y2 yst x y]
  apply fp2At_eq_of_loads
  all_goals
    unfold onCurveStateAfterConstant
    change loadWord (storeWord (storeWord (storeWord (storeWord
      (onCurveStateAfterX3 yst x y).memory 2432 0) 2464 4) 2496 0) 2528 4)
      _ = _
    repeat' rw [loadWord_storeWord_disjoint _ _ _ _ (by norm_num)]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
