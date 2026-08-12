import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveY2

set_option warningAsError true

/-! # Lawful `x²` phase of frozen G2ADD `onCurve` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private theorem onCurveStateAfterY2_fp2At_low (yst : EvmState)
    (x y : U256)
    (hxEnd : x.toNat + 96 < 2 ^ 256) (hxLow : x.toNat + 128 ≤ 1024) :
    fp2At (onCurveStateAfterY2 yst y) x = fp2At yst x := by
  exact fp2MulFinalState_fp2At_before_scratch yst
    (BitVec.ofNat 256 2048) y y x hxEnd hxLow (by norm_num) (by norm_num)

theorem onCurveX2_canonical (yst : EvmState) (x y : U256)
    (hx : Fp2.Canonical (fp2At yst x))
    (hxEnd : x.toNat + 96 < 2 ^ 256) (hxLow : x.toNat + 128 ≤ 1024) :
    Fp2.Canonical (fp2At (onCurveStateAfterX2 yst x y)
      (BitVec.ofNat 256 2176)) := by
  let s := onCurveStateAfterY2 yst y
  have hpres := onCurveStateAfterY2_fp2At_low yst x y hxEnd hxLow
  exact fp2MulFinalState_canonical_of_low s (BitVec.ofNat 256 2176) x x
    (hpres.symm ▸ hx) (hpres.symm ▸ hx)
    hxEnd hxLow hxEnd hxLow (by norm_num) (by norm_num)

theorem onCurveX2_toLawful (yst : EvmState) (x y : U256)
    (hx : Fp2.Canonical (fp2At yst x))
    (hxEnd : x.toNat + 96 < 2 ^ 256) (hxLow : x.toNat + 128 ≤ 1024) :
    Fp2.toLawful (fp2At (onCurveStateAfterX2 yst x y)
      (BitVec.ofNat 256 2176)) = Fp2.toLawful (fp2At yst x) ^ 2 := by
  let s := onCurveStateAfterY2 yst y
  have hpres := onCurveStateAfterY2_fp2At_low yst x y hxEnd hxLow
  rw [pow_two, ← congrArg Fp2.toLawful hpres,
    onCurveStateAfterX2]
  exact fp2MulFinalState_toLawful_mul_of_low s
    (BitVec.ofNat 256 2176) x x (hpres.symm ▸ hx) (hpres.symm ▸ hx)
    hxEnd hxLow hxEnd hxLow (by norm_num) (by norm_num)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
