import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveHighInputs

set_option warningAsError true

/-! # Lawful `x³` phase of frozen G2ADD `onCurve` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private theorem onCurveStateAfterX2_fp2At_x (yst : EvmState) (x y : U256)
    (hxEnd : x.toNat + 96 < 2 ^ 256) (hxLow : x.toNat + 128 ≤ 1024) :
    fp2At (onCurveStateAfterX2 yst x y) x = fp2At yst x := by
  have hy2 := fp2MulFinalState_fp2At_before_scratch yst
    (BitVec.ofNat 256 2048) y y x hxEnd hxLow (by norm_num) (by norm_num)
  have hx2 := fp2MulFinalState_fp2At_before_scratch
    (onCurveStateAfterY2 yst y) (BitVec.ofNat 256 2176) x x x
    hxEnd hxLow (by norm_num) (by norm_num)
  exact hx2.trans hy2

private theorem onCurveX3_leftInput (yst : EvmState) (x y : U256) :
    fp2MulLeftInput (onCurveStateAfterX2 yst x y)
      (BitVec.ofNat 256 2176) x =
    fp2At (onCurveStateAfterX2 yst x y) (BitVec.ofNat 256 2176) :=
  fp2MulLeftInput_eq_fp2At_of_high _ _ _ (by norm_num) (by norm_num)

private theorem onCurveX3_rightInput (yst : EvmState) (x y : U256)
    (hxEnd : x.toNat + 96 < 2 ^ 256) (hxLow : x.toNat + 128 ≤ 1024) :
    fp2MulRightInput (onCurveStateAfterX2 yst x y)
      (BitVec.ofNat 256 2176) x = fp2At yst x := by
  rw [fp2MulRightInput_eq_fp2At_of_low _ _ _ hxEnd hxLow,
    onCurveStateAfterX2_fp2At_x yst x y hxEnd hxLow]

private theorem onCurveX3_scheduledLeft (yst : EvmState) (x y : U256) :
    fp2At (fp2MulAfterRealStores (onCurveStateAfterX2 yst x y)
      (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2176) x)
      (BitVec.ofNat 256 2176) =
    fp2MulLeftInput (onCurveStateAfterX2 yst x y)
      (BitVec.ofNat 256 2176) x :=
  fp2MulScheduledLeft_eq_of_high_before_out _ _ _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem onCurveX3_scheduledRight (yst : EvmState) (x y : U256)
    (hxEnd : x.toNat + 96 < 2 ^ 256) (hxLow : x.toNat + 128 ≤ 1024) :
    fp2At (fp2MulAfterSumAStores (onCurveStateAfterX2 yst x y)
      (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2176) x) x =
    fp2MulRightInput (onCurveStateAfterX2 yst x y)
      (BitVec.ofNat 256 2176) x :=
  fp2MulScheduledRight_eq_of_low _ _ _ _ hxEnd hxLow
    (by norm_num) (by norm_num)

theorem onCurveX3_canonical (yst : EvmState) (x y : U256)
    (hx : Fp2.Canonical (fp2At yst x))
    (hxEnd : x.toNat + 96 < 2 ^ 256) (hxLow : x.toNat + 128 ≤ 1024) :
    Fp2.Canonical (fp2At (onCurveStateAfterX3 yst x y)
      (BitVec.ofNat 256 2304)) := by
  apply fp2MulFinalState_canonical
  · rw [onCurveX3_leftInput]
    exact onCurveX2_canonical yst x y hx hxEnd hxLow
  · rw [onCurveX3_rightInput yst x y hxEnd hxLow]
    exact hx
  · exact onCurveX3_scheduledLeft yst x y
  · exact onCurveX3_scheduledRight yst x y hxEnd hxLow
  · norm_num
  · norm_num

theorem onCurveX3_toLawful (yst : EvmState) (x y : U256)
    (hx : Fp2.Canonical (fp2At yst x))
    (hxEnd : x.toNat + 96 < 2 ^ 256) (hxLow : x.toNat + 128 ≤ 1024) :
    Fp2.toLawful (fp2At (onCurveStateAfterX3 yst x y)
      (BitVec.ofNat 256 2304)) = Fp2.toLawful (fp2At yst x) ^ 3 := by
  have h := fp2MulFinalState_toLawful_mul
    (onCurveStateAfterX2 yst x y) (BitVec.ofNat 256 2304)
    (BitVec.ofNat 256 2176) x
    (by rw [onCurveX3_leftInput]; exact onCurveX2_canonical yst x y hx hxEnd hxLow)
    (by rw [onCurveX3_rightInput yst x y hxEnd hxLow]; exact hx)
    (onCurveX3_scheduledLeft yst x y)
    (onCurveX3_scheduledRight yst x y hxEnd hxLow)
    (by norm_num) (by norm_num)
  rw [onCurveX3_leftInput, onCurveX3_rightInput yst x y hxEnd hxLow,
    onCurveX2_toLawful yst x y hx hxEnd hxLow] at h
  simpa [onCurveStateAfterX3, pow_succ] using h

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
