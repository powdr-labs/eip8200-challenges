import Challenge.Bls12381.ProofSupport.FpBarrett
import Challenge.Bls12381.ProofSupport.FpWordBridge

set_option warningAsError true

/-!
# BLS12-381 Barrett multiple and initial remainder

This module models the exact low-two-word `q * p` schedule and the following
borrow-propagating subtraction from `(r1:r0)` in `Fp.sol`.
-/

namespace Challenge.Bls12381.ProofSupport.Fp

/-- View the source's two quotient words as a generic low/high pair. -/
def quotientWords (product : SchoolbookProduct) :
    Challenge.EvmProof.Limbs.WideProduct :=
  { hi := (barrettQuotient product).q1
    lo := (barrettQuotient product).q0 }

/-- Exact source schedule for the low two words of `q * p`: full-multiply
`Q0 * p0`, then add the two cross terms into its high word. -/
def barrettMultipleLow (product : SchoolbookProduct) :
    Challenge.EvmProof.Limbs.WideProduct :=
  Challenge.EvmProof.Limbs.mulWideLow256 (quotientWords product) modulusWide

/-- The low two product words `(r1:r0)` consumed by the source subtraction. -/
def productLowWords (product : SchoolbookProduct) :
    Challenge.EvmProof.Limbs.WideProduct :=
  { hi := product.r1, lo := product.r0 }

/-- Exact initial remainder schedule from `Fp.sol`, including the low-word
borrow propagated through the two high-word `SUB`s. -/
def barrettRemainder (product : SchoolbookProduct) :
    Challenge.EvmProof.Limbs.WideProduct :=
  Challenge.EvmProof.Limbs.subWide256
    (productLowWords product) (barrettMultipleLow product)

@[simp] theorem quotientWords_value (product : SchoolbookProduct) :
    (quotientWords product).value = (barrettQuotient product).value := rfl

/-- The source schedule reconstructs the low two words of the mathematical
multiple `q * p`. -/
theorem value_barrettMultipleLow (product : SchoolbookProduct) :
    (barrettMultipleLow product).value =
      ((barrettQuotient product).value *
        EvmSemantics.Crypto.Bls12381.p) %
          Challenge.EvmProof.Limbs.radix ^ 2 := by
  unfold barrettMultipleLow
  rw [Challenge.EvmProof.Limbs.mulWideLow256_value,
    quotientWords_value, modulusWide_value]

/-- The source operand `(r1:r0)` is the full three-word product modulo two
words. -/
theorem value_productLowWords (product : SchoolbookProduct) :
    (productLowWords product).value =
      product.value % Challenge.EvmProof.Limbs.radix ^ 2 := by
  have hr0 := product.r0.val.isLt
  have hr1 := product.r1.val.isLt
  change product.r0.toNat < Challenge.EvmProof.Limbs.radix at hr0
  change product.r1.toNat < Challenge.EvmProof.Limbs.radix at hr1
  have hlow : product.r0.toNat + Challenge.EvmProof.Limbs.radix *
      product.r1.toNat < Challenge.EvmProof.Limbs.radix ^ 2 := by
    nlinarith
  unfold productLowWords Challenge.EvmProof.Limbs.WideProduct.value
  unfold SchoolbookProduct.value
  rw [show product.r0.toNat + Challenge.EvmProof.Limbs.radix *
        product.r1.toNat + Challenge.EvmProof.Limbs.radix ^ 2 *
          product.r2.toNat =
      (product.r0.toNat + Challenge.EvmProof.Limbs.radix *
        product.r1.toNat) + Challenge.EvmProof.Limbs.radix ^ 2 *
          product.r2.toNat by ring]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]

/-- For products below `p²`, the exact source subtraction reconstructs the
mathematical Barrett remainder. -/
theorem value_barrettRemainder (product : SchoolbookProduct)
    (hproduct : product.value < EvmSemantics.Crypto.Bls12381.p ^ 2) :
    (barrettRemainder product).value =
      product.value -
        (barrettQuotient product).value *
          EvmSemantics.Crypto.Bls12381.p := by
  let modulus := EvmSemantics.Crypto.Bls12381.p
  let radixSq := Challenge.EvmProof.Limbs.radix ^ 2
  let x := product.value
  let multiple := (barrettQuotient product).value * modulus
  let remainder := x - multiple
  have hmultiple : multiple ≤ x := by
    exact barrettQuotient_mul_modulus_le product
  have hremainder : remainder < radixSq := by
    have hbarrett := barrettRemainder_lt_three_mul_modulus product hproduct
    have hthreeModulus : 3 * modulus < radixSq := by
      dsimp only [modulus, radixSq]
      norm_num [Challenge.EvmProof.Limbs.radix,
        EvmSemantics.Crypto.Bls12381.p,
        EvmSemantics.Crypto.Bls12381.absU]
    exact hbarrett.trans hthreeModulus
  have hmultipleMod : multiple % radixSq < radixSq := by
    exact Nat.mod_lt multiple (pow_pos Challenge.EvmProof.Limbs.radix_pos 2)
  have hsum : remainder + multiple % radixSq < 2 * radixSq := by omega
  have hxMod : x % radixSq = (remainder + multiple % radixSq) % radixSq := by
    calc
      x % radixSq = (remainder + multiple) % radixSq := by
        rw [Nat.sub_add_cancel hmultiple]
      _ = (remainder % radixSq + multiple % radixSq) % radixSq := by
        exact Nat.add_mod remainder multiple radixSq
      _ = (remainder + multiple % radixSq) % radixSq := by
        rw [Nat.mod_eq_of_lt hremainder]
  unfold barrettRemainder
  rw [Challenge.EvmProof.Limbs.subWide256_value_mod,
    value_productLowWords, value_barrettMultipleLow]
  change (x % radixSq + radixSq - multiple % radixSq) % radixSq = remainder
  rw [hxMod, Challenge.EvmProof.Limbs.mod_eq_cond_sub hsum]
  by_cases hwrap : remainder + multiple % radixSq < radixSq
  · rw [if_pos hwrap]
    have hrearrange : remainder + multiple % radixSq + radixSq -
        multiple % radixSq = radixSq + remainder := by omega
    rw [hrearrange, Nat.add_mod, Nat.mod_self, Nat.zero_add]
    simpa using Nat.mod_eq_of_lt hremainder
  · rw [if_neg hwrap]
    have hrearrange : remainder + multiple % radixSq - radixSq + radixSq -
        multiple % radixSq = remainder := by omega
    rw [hrearrange, Nat.mod_eq_of_lt hremainder]

end Challenge.Bls12381.ProofSupport.Fp
