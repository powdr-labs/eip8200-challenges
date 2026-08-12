import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddPreservation
import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveY2Preservation

set_option warningAsError true

/-! # Correctness of frozen G2ADD `onCurve` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private theorem onCurveAdd_y2 (yst : EvmState) (x y : U256) :
    fp2At (onCurveStateAfterAdd yst x y) (BitVec.ofNat 256 2048) =
      fp2At (onCurveStateAfterY2 yst y) (BitVec.ofNat 256 2048) := by
  rw [onCurveStateAfterAdd,
    fp2AddContractState_fp2At_before_out
      (onCurveStateAfterConstant yst x y) (BitVec.ofNat 256 2304)
      (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2432)
      (BitVec.ofNat 256 2048) (by norm_num) (by norm_num) (by norm_num),
    onCurveConstant_y2]

theorem onCurveResult_eq_one_iff (yst : EvmState) (x y : U256)
    (hx : Fp2.Canonical (fp2At yst x))
    (hy : Fp2.Canonical (fp2At yst y))
    (hxEnd : x.toNat + 96 < 2 ^ 256) (hxLow : x.toNat + 128 ≤ 1024)
    (hyEnd : y.toNat + 96 < 2 ^ 256) (hyLow : y.toNat + 128 ≤ 1024) :
    onCurveResult yst x y = 1 ↔
      G2Affine.OnCurve (.affine
        (Fp2.toLawful (fp2At yst x)) (Fp2.toLawful (fp2At yst y))) := by
  apply onCurveResult_eq_one_iff_of_lawful_outputs
  · rw [onCurveAdd_y2]
    exact onCurveY2_toLawful yst y hy hyEnd hyLow
  · exact onCurveRhs_toLawful yst x y hx hxEnd hxLow
  · rw [onCurveAdd_y2]
    exact onCurveY2_canonical yst y hy hyEnd hyLow
  · exact onCurveRhs_canonical yst x y hx hxEnd hxLow

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
