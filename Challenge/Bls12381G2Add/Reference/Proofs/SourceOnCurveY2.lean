import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveMulLawful
import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveResult

set_option warningAsError true

/-! # Lawful `y²` phase of frozen G2ADD `onCurve` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem onCurveY2_canonical (yst : EvmState) (y : U256)
    (hy : Fp2.Canonical (fp2At yst y))
    (hyEnd : y.toNat + 96 < 2 ^ 256) (hyLow : y.toNat + 128 ≤ 1024) :
    Fp2.Canonical (fp2At (onCurveStateAfterY2 yst y)
      (BitVec.ofNat 256 2048)) := by
  exact (fp2Mul_low_contract yst (BitVec.ofNat 256 2048) y y
    hy hy hyEnd hyLow hyEnd hyLow (by norm_num) (by norm_num)).output_canonical

theorem onCurveY2_toLawful (yst : EvmState) (y : U256)
    (hy : Fp2.Canonical (fp2At yst y))
    (hyEnd : y.toNat + 96 < 2 ^ 256) (hyLow : y.toNat + 128 ≤ 1024) :
    Fp2.toLawful (fp2At (onCurveStateAfterY2 yst y)
      (BitVec.ofNat 256 2048)) = Fp2.toLawful (fp2At yst y) ^ 2 := by
  rw [pow_two]
  exact (fp2Mul_low_contract yst (BitVec.ofNat 256 2048) y y
    hy hy hyEnd hyLow hyEnd hyLow (by norm_num)
    (by norm_num)).output_toLawful_mul

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
