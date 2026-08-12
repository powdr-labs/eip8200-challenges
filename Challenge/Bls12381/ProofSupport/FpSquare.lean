import Challenge.Bls12381.ProofSupport.FpMul
import Challenge.Bls12381.ProofSupport.FpRepresentation
import Challenge.Bls12381.ProofSupport.FpWordBridge

set_option warningAsError true

/-!
# BLS12-381 specialized canonical squaring

This module follows `Fp.sol`'s three-partial-product square schedule. The
cross product is doubled with the exact `SHL`/`SHR`/`OR` word splice before
the already-verified Barrett reduction is applied.
-/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics
open EvmSemantics.Crypto.Bls12381

/-- The exact three-partial-product squaring schedule from `Fp.sol`: compute
`a0²`, double the full `a1*a0` cross product with shifts, compute `a1²`,
then accumulate the middle word and its carry. -/
def squareSchoolbookProduct (a : Limbs) : SchoolbookProduct :=
  let p00 := Challenge.EvmProof.Limbs.fullMul256 a.lo a.lo
  let doubledCross := Challenge.EvmProof.Limbs.doubleWide256
    (Challenge.EvmProof.Limbs.fullMul256 a.hi a.lo)
  let middle := Challenge.EvmProof.Limbs.addTwo256 p00.hi doubledCross.lo
  let r2 := doubledCross.hi + (a.hi * a.hi) + middle.carry
  { r2 := r2, r1 := middle.word, r0 := p00.lo }

/-- Natural value accumulated into the source's top square word before its
two wrapped additions. -/
def squareSchoolbookTop (a : Limbs) : Nat :=
  let cross := Challenge.EvmProof.Limbs.fullMul256 a.hi a.lo
  let doubledCross := Challenge.EvmProof.Limbs.doubleWide256 cross
  let p00 := Challenge.EvmProof.Limbs.fullMul256 a.lo a.lo
  let middle := Challenge.EvmProof.Limbs.addTwo256 p00.hi doubledCross.lo
  doubledCross.hi.toNat + a.hi.toNat * a.hi.toNat + middle.carry.toNat

/-- A canonical high limb is only 128 bits, so doubling its full product with
the low limb cannot overflow the two-word cross-product buffer. -/
theorem cross_double_fits {a : Limbs} (ha : Canonical a) :
    2 * (Challenge.EvmProof.Limbs.fullMul256 a.hi a.lo).value <
      Challenge.EvmProof.Limbs.radix ^ 2 := by
  rw [Challenge.EvmProof.Limbs.fullMul256_value]
  have hhi := ha.1
  have hlo := a.lo.val.isLt
  change a.lo.toNat < Challenge.EvmProof.Limbs.radix at hlo
  have h128 : 2 * 2 ^ 128 < Challenge.EvmProof.Limbs.radix := by
    norm_num [Challenge.EvmProof.Limbs.radix]
  nlinarith

/-- The mathematical top word of a canonical square fits in one EVM word. -/
theorem squareSchoolbookTop_lt {a : Limbs} (ha : Canonical a) :
    squareSchoolbookTop a < Challenge.EvmProof.Limbs.radix := by
  let p00 := Challenge.EvmProof.Limbs.fullMul256 a.lo a.lo
  let cross := Challenge.EvmProof.Limbs.fullMul256 a.hi a.lo
  let doubledCross := Challenge.EvmProof.Limbs.doubleWide256 cross
  let middle := Challenge.EvmProof.Limbs.addTwo256 p00.hi doubledCross.lo
  let topNat := doubledCross.hi.toNat + a.hi.toNat * a.hi.toNat +
    middle.carry.toNat
  have h00 := Challenge.EvmProof.Limbs.fullMul256_value a.lo a.lo
  have hcross := Challenge.EvmProof.Limbs.fullMul256_value a.hi a.lo
  have hdouble := Challenge.EvmProof.Limbs.doubleWide256_value cross
    (cross_double_fits ha)
  have hmiddle : middle.value =
      p00.hi.toNat + doubledCross.lo.toNat := by
    exact Challenge.EvmProof.Limbs.addTwo256_value p00.hi doubledCross.lo
  change p00.value = a.lo.toNat * a.lo.toNat at h00
  change cross.value = a.hi.toNat * a.lo.toNat at hcross
  change doubledCross.value = 2 * cross.value at hdouble
  have hreconstruct :
      value a ^ 2 =
        p00.lo.toNat + Challenge.EvmProof.Limbs.radix * middle.word.toNat +
          Challenge.EvmProof.Limbs.radix ^ 2 * topNat := by
    unfold Challenge.EvmProof.Limbs.WideProduct.value at h00 hcross hdouble
    unfold Challenge.EvmProof.Limbs.WordSum.value at hmiddle
    calc
      value a ^ 2 =
          a.lo.toNat * a.lo.toNat + Challenge.EvmProof.Limbs.radix *
            (2 * (a.hi.toNat * a.lo.toNat)) +
          Challenge.EvmProof.Limbs.radix ^ 2 *
            (a.hi.toNat * a.hi.toNat) := by
              unfold value
              ring
      _ = (p00.lo.toNat + Challenge.EvmProof.Limbs.radix * p00.hi.toNat) +
          Challenge.EvmProof.Limbs.radix *
            (doubledCross.lo.toNat + Challenge.EvmProof.Limbs.radix *
              doubledCross.hi.toNat) +
          Challenge.EvmProof.Limbs.radix ^ 2 *
            (a.hi.toNat * a.hi.toNat) := by rw [h00, hdouble, hcross]
      _ = p00.lo.toNat + Challenge.EvmProof.Limbs.radix *
            (p00.hi.toNat + doubledCross.lo.toNat) +
          Challenge.EvmProof.Limbs.radix ^ 2 *
            (doubledCross.hi.toNat + a.hi.toNat * a.hi.toNat) := by ring
      _ = p00.lo.toNat + Challenge.EvmProof.Limbs.radix *
            (middle.word.toNat + Challenge.EvmProof.Limbs.radix *
              middle.carry.toNat) +
          Challenge.EvmProof.Limbs.radix ^ 2 *
            (doubledCross.hi.toNat + a.hi.toNat * a.hi.toNat) := by rw [hmiddle]
      _ = p00.lo.toNat + Challenge.EvmProof.Limbs.radix * middle.word.toNat +
          Challenge.EvmProof.Limbs.radix ^ 2 * topNat := by
            unfold topNat
            ring
  have hpSq : p ^ 2 < Challenge.EvmProof.Limbs.radix ^ 3 := by
    norm_num [p, absU, Challenge.EvmProof.Limbs.radix]
  have hsquare : value a ^ 2 < p ^ 2 := by
    exact Nat.pow_lt_pow_left ha.2 (by omega)
  have htop : topNat < Challenge.EvmProof.Limbs.radix := by
    rw [hreconstruct] at hsquare
    nlinarith [hsquare.trans hpSq]
  change topNat < Challenge.EvmProof.Limbs.radix
  exact htop

/-- The source's wrapped top-word additions do not overflow for a canonical
operand, so the concrete `r2` word equals the mathematical top value. -/
theorem squareSchoolbookProduct_r2_value {a : Limbs} (ha : Canonical a) :
    (squareSchoolbookProduct a).r2.toNat = squareSchoolbookTop a := by
  let p00 := Challenge.EvmProof.Limbs.fullMul256 a.lo a.lo
  let cross := Challenge.EvmProof.Limbs.fullMul256 a.hi a.lo
  let doubledCross := Challenge.EvmProof.Limbs.doubleWide256 cross
  let middle := Challenge.EvmProof.Limbs.addTwo256 p00.hi doubledCross.lo
  have htop := squareSchoolbookTop_lt ha
  change doubledCross.hi.toNat + a.hi.toNat * a.hi.toNat + middle.carry.toNat <
    Challenge.EvmProof.Limbs.radix at htop
  have hmidBound : a.hi.toNat * a.hi.toNat <
      Challenge.EvmProof.Limbs.radix := by
    have hhi := ha.1
    have hradix : 2 ^ 128 * 2 ^ 128 = Challenge.EvmProof.Limbs.radix := by
      norm_num [Challenge.EvmProof.Limbs.radix]
    nlinarith
  have hmid : (a.hi * a.hi).toNat = a.hi.toNat * a.hi.toNat := by
    rw [Challenge.EvmProof.Word.word_toNat_mul]
    rw [show 2 ^ 256 = Challenge.EvmProof.Limbs.radix by rfl,
      Nat.mod_eq_of_lt hmidBound]
  change (doubledCross.hi + a.hi * a.hi + middle.carry).toNat =
    squareSchoolbookTop a
  simp only [Challenge.EvmProof.Word.word_toNat_add]
  rw [hmid, show 2 ^ 256 = Challenge.EvmProof.Limbs.radix by rfl]
  have hfirst : doubledCross.hi.toNat + a.hi.toNat * a.hi.toNat <
      Challenge.EvmProof.Limbs.radix := by omega
  rw [Nat.mod_eq_of_lt hfirst, Nat.mod_eq_of_lt htop]
  simp [squareSchoolbookTop, p00, cross, doubledCross, middle, Nat.add_assoc]

/-- The concrete top word is range-valid. -/
theorem squareSchoolbookProduct_r2_lt {a : Limbs} (ha : Canonical a) :
    (squareSchoolbookProduct a).r2.toNat < Challenge.EvmProof.Limbs.radix := by
  rw [squareSchoolbookProduct_r2_value ha]
  exact squareSchoolbookTop_lt ha

/-- Reconstructing all three source words yields the operand's natural
square. -/
theorem value_squareSchoolbookProduct {a : Limbs} (ha : Canonical a) :
    (squareSchoolbookProduct a).value = value a ^ 2 := by
  let p00 := Challenge.EvmProof.Limbs.fullMul256 a.lo a.lo
  let cross := Challenge.EvmProof.Limbs.fullMul256 a.hi a.lo
  let doubledCross := Challenge.EvmProof.Limbs.doubleWide256 cross
  let middle := Challenge.EvmProof.Limbs.addTwo256 p00.hi doubledCross.lo
  have h00 := Challenge.EvmProof.Limbs.fullMul256_value a.lo a.lo
  have hcross := Challenge.EvmProof.Limbs.fullMul256_value a.hi a.lo
  have hdouble := Challenge.EvmProof.Limbs.doubleWide256_value cross
    (cross_double_fits ha)
  have hmiddle : middle.value =
      p00.hi.toNat + doubledCross.lo.toNat := by
    exact Challenge.EvmProof.Limbs.addTwo256_value p00.hi doubledCross.lo
  have hr2 := squareSchoolbookProduct_r2_value ha
  change p00.value = a.lo.toNat * a.lo.toNat at h00
  change cross.value = a.hi.toNat * a.lo.toNat at hcross
  change doubledCross.value = 2 * cross.value at hdouble
  unfold SchoolbookProduct.value
  change p00.lo.toNat + Challenge.EvmProof.Limbs.radix * middle.word.toNat +
      Challenge.EvmProof.Limbs.radix ^ 2 *
        (squareSchoolbookProduct a).r2.toNat = value a ^ 2
  rw [hr2]
  change p00.lo.toNat + Challenge.EvmProof.Limbs.radix * middle.word.toNat +
      Challenge.EvmProof.Limbs.radix ^ 2 *
        (doubledCross.hi.toNat + a.hi.toNat * a.hi.toNat + middle.carry.toNat) =
      value a ^ 2
  unfold Challenge.EvmProof.Limbs.WideProduct.value at h00 hcross hdouble
  unfold Challenge.EvmProof.Limbs.WordSum.value at hmiddle
  unfold value
  nlinarith [hmiddle]

/-- Source-faithful specialized squaring followed by the fixed Barrett
reduction and its two conditional corrections. -/
def squareCanonical (a : Limbs) : Limbs :=
  ofWide (barrettReduce (squareSchoolbookProduct a))

/-- The specialized word-level square reconstructs reduction modulo the BLS
base-field modulus. -/
theorem value_squareCanonical {a : Limbs} (ha : Canonical a) :
    value (squareCanonical a) = value a ^ 2 % p := by
  let product := squareSchoolbookProduct a
  have hproductValue : product.value = value a ^ 2 :=
    value_squareSchoolbookProduct ha
  have hproduct : product.value < p ^ 2 := by
    rw [hproductValue]
    exact Nat.pow_lt_pow_left ha.2 (by omega)
  unfold squareCanonical
  rw [value_ofWide, value_barrettReduce product hproduct, hproductValue]

/-- Specialized squaring returns a canonical 48-byte field element. -/
theorem canonical_squareCanonical {a : Limbs} (ha : Canonical a) :
    Canonical (squareCanonical a) := by
  have hvalue : value (squareCanonical a) < p := by
    rw [value_squareCanonical ha]
    exact Nat.mod_lt _ (by norm_num [p, absU])
  exact canonical_of_value_lt _ hvalue

/-- Specialized squaring refines squaring in the pinned `Fin p` carrier. -/
theorem refines_squareCanonical {a : Limbs} (ha : Canonical a) :
    Refines (squareCanonical a) (toField a ^ 2) := by
  apply Fin.ext
  simp [toField, value_squareCanonical ha, pow_two, Fin.mul_def, Nat.mul_mod]

/-- Field projection of the specialized concrete square. -/
@[simp] theorem toField_squareCanonical {a : Limbs} (ha : Canonical a) :
    toField (squareCanonical a) = toField a ^ 2 := by
  simpa only [Refines] using refines_squareCanonical ha

end Challenge.Bls12381.ProofSupport.Fp
