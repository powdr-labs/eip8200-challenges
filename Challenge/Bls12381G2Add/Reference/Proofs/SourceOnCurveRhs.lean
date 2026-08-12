import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveConstantMemory

set_option warningAsError true

/-! # Lawful right-hand side of frozen G2ADD `onCurve` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem onCurveRhs_canonical (yst : EvmState) (x y : U256)
    (hx : Fp2.Canonical (fp2At yst x))
    (hxEnd : x.toNat + 96 < 2 ^ 256) (hxLow : x.toNat + 128 ≤ 1024) :
    Fp2.Canonical (fp2At (onCurveStateAfterAdd yst x y)
      (BitVec.ofNat 256 2304)) := by
  rw [onCurveStateAfterAdd,
    fp2AddContractState_output_inplace_right_after _ _ _
      (by norm_num) (by norm_num) (by norm_num),
    onCurveConstant_x3, onCurveConstant_value]
  apply Fp2.canonical_addSource
  · exact onCurveX3_canonical yst x y hx hxEnd hxLow
  · exact onCurveTwistB_canonical

theorem onCurveRhs_toLawful (yst : EvmState) (x y : U256)
    (hx : Fp2.Canonical (fp2At yst x))
    (hxEnd : x.toNat + 96 < 2 ^ 256) (hxLow : x.toNat + 128 ≤ 1024) :
    Fp2.toLawful (fp2At (onCurveStateAfterAdd yst x y)
        (BitVec.ofNat 256 2304)) =
      Fp2.toLawful (fp2At yst x) ^ 3 + G2Affine.curve.b := by
  have ha : Fp2.Canonical (fp2At (onCurveStateAfterConstant yst x y)
      (BitVec.ofNat 256 2304)) := by
    rw [onCurveConstant_x3]
    exact onCurveX3_canonical yst x y hx hxEnd hxLow
  have hb : Fp2.Canonical (fp2At (onCurveStateAfterConstant yst x y)
      (BitVec.ofNat 256 2432)) := by
    rw [onCurveConstant_value]
    exact onCurveTwistB_canonical
  rw [onCurveStateAfterAdd,
    fp2AddContractState_output_inplace_right_after _ _ _
      (by norm_num) (by norm_num) (by norm_num),
    Fp2.toLawful_addSource ha hb]
  rw [onCurveConstant_x3, onCurveConstant_value,
    onCurveX3_toLawful yst x y hx hxEnd hxLow, onCurveTwistB_toLawful]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
