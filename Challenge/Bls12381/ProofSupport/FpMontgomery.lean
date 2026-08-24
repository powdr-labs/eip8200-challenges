import Challenge.Bls12381.ProofSupport.FpConstants

set_option warningAsError true

/-!
# BLS12-381 source-specific Montgomery multiplication

This module models the two-word CIOS `montMul2` routine nested in
`Fp.sol::_modexp`.  The constants and instruction schedule remain separate
from the small base-field representation boundary in `Fp.lean`.
-/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics
open EvmSemantics.Crypto.Bls12381

/-! ## Constants pinned by `Fp.sol::_modexp.montMul2` -/

/-- The source's `-n₀⁻¹ mod 2²⁵⁶` Montgomery reduction constant. -/
def montgomeryN0Inv : UInt256 := UInt256.ofNat
  0x19ecca0e8eb2db4c16ef2ef0c8e30b48286adb92d9d113e889f3fffcfffcfffd

/-- Low word of the source's `R² mod p`, where Montgomery `R = 2⁵¹²`. -/
def montgomeryR2Lo : UInt256 := UInt256.ofNat
  0xcc0868ce6a76590c76e5bc3ff951c543861c23693de6a351fb73eaead26ebe58

/-- High word of the source's `R² mod p`, where Montgomery `R = 2⁵¹²`. -/
def montgomeryR2Hi : UInt256 := UInt256.ofNat
  0x0010a8c1a49a064ff0a85a3f35446d0b

/-- Natural reconstruction of the two hardcoded `R²` words. -/
def montgomeryR2Value : Nat :=
  montgomeryR2Lo.toNat + Challenge.EvmProof.Limbs.radix * montgomeryR2Hi.toNat

theorem montgomeryN0Inv_value : montgomeryN0Inv.toNat =
    0x19ecca0e8eb2db4c16ef2ef0c8e30b48286adb92d9d113e889f3fffcfffcfffd := by
  norm_num [montgomeryN0Inv, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem montgomeryR2Lo_value : montgomeryR2Lo.toNat =
    0xcc0868ce6a76590c76e5bc3ff951c543861c23693de6a351fb73eaead26ebe58 := by
  norm_num [montgomeryR2Lo, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem montgomeryR2Hi_value : montgomeryR2Hi.toNat =
    0x0010a8c1a49a064ff0a85a3f35446d0b := by
  norm_num [montgomeryR2Hi, Challenge.EvmProof.Word.word_toNat_ofNat]

/-- The hardcoded reduction word really is `-n₀⁻¹` modulo one EVM word. -/
theorem montgomeryN0Inv_spec :
    (montgomeryN0Inv.toNat * modulusLo.toNat) %
        Challenge.EvmProof.Limbs.radix =
      Challenge.EvmProof.Limbs.radix - 1 := by
  norm_num [montgomeryN0Inv, modulusLo,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Limbs.radix]

/-- The two source literals reconstruct `R² mod p` for two-word Montgomery
radix `R = (2²⁵⁶)²`. -/
theorem montgomeryR2_spec : montgomeryR2Value =
    Challenge.EvmProof.Limbs.radix ^ 4 % p := by
  norm_num [montgomeryR2Value, montgomeryR2Lo, montgomeryR2Hi,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Limbs.radix, p, absU]

/-! ## First multiply accumulation (`i = 0`) -/

/-- The three source temporaries, ordered from least to most significant word. -/
structure MontgomeryState where
  t0 : UInt256
  t1 : UInt256
  t2 : UInt256
deriving DecidableEq, Repr

namespace MontgomeryState

/-- Natural reconstruction of the three source temporaries. -/
def value (state : MontgomeryState) : Nat :=
  state.t0.toNat + Challenge.EvmProof.Limbs.radix * state.t1.toNat +
    Challenge.EvmProof.Limbs.radix ^ 2 * state.t2.toNat

end MontgomeryState

/-- The exact initial two-full-product schedule for iteration `i = 0`.
The `LT(s, lo)` overflow test is represented by `addTwo256 lo carry`, keeping
the source operand order. -/
def montgomeryAccumulateZero (x0 y0 y1 : UInt256) : MontgomeryState :=
  let p0 := Challenge.EvmProof.Limbs.fullMul256 x0 y0
  let p1 := Challenge.EvmProof.Limbs.fullMul256 x0 y1
  let middle := Challenge.EvmProof.Limbs.addTwo256 p1.lo p0.hi
  { t0 := p0.lo, t1 := middle.word, t2 := p1.hi + middle.carry }

/-- The unwrapped natural top accumulator used to prove the final source
`ADD` cannot overflow. -/
def montgomeryAccumulateZeroTop (x0 y0 y1 : UInt256) : Nat :=
  let p0 := Challenge.EvmProof.Limbs.fullMul256 x0 y0
  let p1 := Challenge.EvmProof.Limbs.fullMul256 x0 y1
  let middle := Challenge.EvmProof.Limbs.addTwo256 p1.lo p0.hi
  p1.hi.toNat + middle.carry.toNat

theorem montgomeryAccumulateZeroTop_lt (x0 y0 y1 : UInt256) :
    montgomeryAccumulateZeroTop x0 y0 y1 <
      Challenge.EvmProof.Limbs.radix := by
  let p0 := Challenge.EvmProof.Limbs.fullMul256 x0 y0
  let p1 := Challenge.EvmProof.Limbs.fullMul256 x0 y1
  let middle := Challenge.EvmProof.Limbs.addTwo256 p1.lo p0.hi
  have hp0 := Challenge.EvmProof.Limbs.fullMul256_value x0 y0
  have hp1 := Challenge.EvmProof.Limbs.fullMul256_value x0 y1
  have hmiddle := Challenge.EvmProof.Limbs.addTwo256_value p1.lo p0.hi
  change p0.lo.toNat + Challenge.EvmProof.Limbs.radix * p0.hi.toNat =
    x0.toNat * y0.toNat at hp0
  change p1.lo.toNat + Challenge.EvmProof.Limbs.radix * p1.hi.toNat =
    x0.toNat * y1.toNat at hp1
  change middle.word.toNat + Challenge.EvmProof.Limbs.radix *
    middle.carry.toNat = p1.lo.toNat + p0.hi.toNat at hmiddle
  have hx := x0.val.isLt
  have hy0 := y0.val.isLt
  have hy1 := y1.val.isLt
  change x0.toNat < Challenge.EvmProof.Limbs.radix at hx
  change y0.toNat < Challenge.EvmProof.Limbs.radix at hy0
  change y1.toNat < Challenge.EvmProof.Limbs.radix at hy1
  have hy : y0.toNat + Challenge.EvmProof.Limbs.radix * y1.toNat <
      Challenge.EvmProof.Limbs.radix ^ 2 := by
    nlinarith
  have hproduct :
      x0.toNat * (y0.toNat + Challenge.EvmProof.Limbs.radix * y1.toNat) <
        Challenge.EvmProof.Limbs.radix ^ 3 := by
    have hmul := Nat.mul_lt_mul_of_lt_of_lt hx hy
    nlinarith
  have hreconstruct :
      x0.toNat * (y0.toNat + Challenge.EvmProof.Limbs.radix * y1.toNat) =
        p0.lo.toNat + Challenge.EvmProof.Limbs.radix * middle.word.toNat +
          Challenge.EvmProof.Limbs.radix ^ 2 *
            (p1.hi.toNat + middle.carry.toNat) := by
    nlinarith [hp0, hp1, hmiddle]
  rw [hreconstruct] at hproduct
  change p1.hi.toNat + middle.carry.toNat <
    Challenge.EvmProof.Limbs.radix
  nlinarith

theorem montgomeryAccumulateZero_top_value (x0 y0 y1 : UInt256) :
    (montgomeryAccumulateZero x0 y0 y1).t2.toNat =
      montgomeryAccumulateZeroTop x0 y0 y1 := by
  let p0 := Challenge.EvmProof.Limbs.fullMul256 x0 y0
  let p1 := Challenge.EvmProof.Limbs.fullMul256 x0 y1
  let middle := Challenge.EvmProof.Limbs.addTwo256 p1.lo p0.hi
  have htop := montgomeryAccumulateZeroTop_lt x0 y0 y1
  change p1.hi.toNat + middle.carry.toNat <
    Challenge.EvmProof.Limbs.radix at htop
  change (p1.hi + middle.carry).toNat =
    montgomeryAccumulateZeroTop x0 y0 y1
  rw [Challenge.EvmProof.Word.word_toNat_add,
    show 2 ^ 256 = Challenge.EvmProof.Limbs.radix by rfl,
    Nat.mod_eq_of_lt htop]
  rfl

theorem montgomeryAccumulateZero_top_lt (x0 y0 y1 : UInt256) :
    (montgomeryAccumulateZero x0 y0 y1).t2.toNat <
      Challenge.EvmProof.Limbs.radix := by
  rw [montgomeryAccumulateZero_top_value]
  exact montgomeryAccumulateZeroTop_lt x0 y0 y1

theorem montgomeryAccumulateZero_value (x0 y0 y1 : UInt256) :
    (montgomeryAccumulateZero x0 y0 y1).value =
      x0.toNat *
        (y0.toNat + Challenge.EvmProof.Limbs.radix * y1.toNat) := by
  let p0 := Challenge.EvmProof.Limbs.fullMul256 x0 y0
  let p1 := Challenge.EvmProof.Limbs.fullMul256 x0 y1
  let middle := Challenge.EvmProof.Limbs.addTwo256 p1.lo p0.hi
  have hp0 := Challenge.EvmProof.Limbs.fullMul256_value x0 y0
  have hp1 := Challenge.EvmProof.Limbs.fullMul256_value x0 y1
  have hmiddle := Challenge.EvmProof.Limbs.addTwo256_value p1.lo p0.hi
  have htop := montgomeryAccumulateZero_top_value x0 y0 y1
  change p0.lo.toNat + Challenge.EvmProof.Limbs.radix * p0.hi.toNat =
    x0.toNat * y0.toNat at hp0
  change p1.lo.toNat + Challenge.EvmProof.Limbs.radix * p1.hi.toNat =
    x0.toNat * y1.toNat at hp1
  change middle.word.toNat + Challenge.EvmProof.Limbs.radix *
    middle.carry.toNat = p1.lo.toNat + p0.hi.toNat at hmiddle
  change p0.lo.toNat + Challenge.EvmProof.Limbs.radix * middle.word.toNat +
    Challenge.EvmProof.Limbs.radix ^ 2 *
      (montgomeryAccumulateZero x0 y0 y1).t2.toNat = _
  rw [htop]
  unfold montgomeryAccumulateZeroTop
  change p0.lo.toNat + Challenge.EvmProof.Limbs.radix * middle.word.toNat +
    Challenge.EvmProof.Limbs.radix ^ 2 *
      (p1.hi.toNat + middle.carry.toNat) = _
  nlinarith [hp0, hp1, hmiddle]

end Challenge.Bls12381.ProofSupport.Fp
