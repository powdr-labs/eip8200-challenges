import Challenge.Bls12381.ProofSupport.FpConstants

set_option warningAsError true

/-!
# BLS12-381 source-specific schoolbook multiplication

This module owns the concrete three-word product schedule and fixed Barrett
constants from `Fp.sol`.  The small `Fp` representation boundary remains free
of implementation-specific multiplication details so the field tower does not
depend on them.
-/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics
open EvmSemantics.Crypto.Bls12381

/-- Three EVM words holding the unreduced product of two canonical base-field
values, least-significant word first. -/
structure SchoolbookProduct where
  r2 : UInt256
  r1 : UInt256
  r0 : UInt256
deriving DecidableEq, Repr

namespace SchoolbookProduct

def value (product : SchoolbookProduct) : Nat :=
  product.r0.toNat + Challenge.EvmProof.Limbs.radix * product.r1.toNat +
    Challenge.EvmProof.Limbs.radix ^ 2 * product.r2.toNat

end SchoolbookProduct

/-- The exact two-limb schoolbook schedule in `Fp.sol`.  Each partial product
uses the source's `MUL`/`MULMOD` full-word idiom and the middle word uses the
same pair of wrapped additions and overflow tests. -/
def schoolbookProduct (a b : Limbs) : SchoolbookProduct :=
  let p00 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.lo
  let p10 := Challenge.EvmProof.Limbs.fullMul256 a.hi b.lo
  let p01 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.hi
  let middle := Challenge.EvmProof.Limbs.addThree256 p00.hi p10.lo p01.lo
  let top := p10.hi + p01.hi + (a.hi * b.hi + middle.carry)
  { r2 := top, r1 := middle.word, r0 := p00.lo }

/-- Natural value accumulated into the source's top product word before the
final wrapped `ADD`s.  Canonical operands make this strictly less than one EVM
word, which is the crucial no-overflow obligation. -/
def schoolbookTop (a b : Limbs) : Nat :=
  let p00 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.lo
  let p10 := Challenge.EvmProof.Limbs.fullMul256 a.hi b.lo
  let p01 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.hi
  let middle := Challenge.EvmProof.Limbs.addThree256 p00.hi p10.lo p01.lo
  p10.hi.toNat + p01.hi.toNat + a.hi.toNat * b.hi.toNat + middle.carry.toNat

/-! ## Fixed Barrett constants from `Fp.sol` -/

def barrettMu0 : UInt256 := UInt256.ofNat
  0xad397b918f6ff20d533b6c08511c60e2757079ace6bd401859778ceb4dabc4f8

def barrettMu1 : UInt256 := UInt256.ofNat
  0x1b82741ff6a0a94bdf4771e0286779d3997167a058f1c07b13e207f56591ba2e

def barrettMu2 : UInt256 := UInt256.ofNat
  0x9d835d2f3cc9e45ce28101b0cc7a6ba29

def barrettMu : Nat :=
  barrettMu0.toNat + Challenge.EvmProof.Limbs.radix * barrettMu1.toNat +
    Challenge.EvmProof.Limbs.radix ^ 2 * barrettMu2.toNat

theorem barrettMu_words :
    barrettMu = barrettMu0.toNat +
      Challenge.EvmProof.Limbs.radix * barrettMu1.toNat +
      Challenge.EvmProof.Limbs.radix ^ 2 * barrettMu2.toNat := rfl

theorem barrettMu_eq_floor :
    barrettMu = Challenge.EvmProof.Limbs.radix ^ 4 / p := by
  norm_num [barrettMu, barrettMu0, barrettMu1, barrettMu2,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Limbs.radix, p, absU]

theorem schoolbookTop_lt {a b : Limbs} (ha : Canonical a) (hb : Canonical b) :
    schoolbookTop a b < Challenge.EvmProof.Limbs.radix := by
  let p00 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.lo
  let p10 := Challenge.EvmProof.Limbs.fullMul256 a.hi b.lo
  let p01 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.hi
  let middle := Challenge.EvmProof.Limbs.addThree256 p00.hi p10.lo p01.lo
  let topNat := p10.hi.toNat + p01.hi.toNat +
    a.hi.toNat * b.hi.toNat + middle.carry.toNat
  have h00 := Challenge.EvmProof.Limbs.fullMul256_value a.lo b.lo
  have h10 := Challenge.EvmProof.Limbs.fullMul256_value a.hi b.lo
  have h01 := Challenge.EvmProof.Limbs.fullMul256_value a.lo b.hi
  have hmiddle := Challenge.EvmProof.Limbs.addThree256_value
    p00.hi p10.lo p01.lo
  change p00.lo.toNat + Challenge.EvmProof.Limbs.radix * p00.hi.toNat =
    a.lo.toNat * b.lo.toNat at h00
  change p10.lo.toNat + Challenge.EvmProof.Limbs.radix * p10.hi.toNat =
    a.hi.toNat * b.lo.toNat at h10
  change p01.lo.toNat + Challenge.EvmProof.Limbs.radix * p01.hi.toNat =
    a.lo.toNat * b.hi.toNat at h01
  change middle.word.toNat + Challenge.EvmProof.Limbs.radix *
    middle.carry.toNat = p00.hi.toNat + p10.lo.toNat + p01.lo.toNat at hmiddle
  have hreconstruct :
      value a * value b =
        p00.lo.toNat + Challenge.EvmProof.Limbs.radix * middle.word.toNat +
          Challenge.EvmProof.Limbs.radix ^ 2 * topNat := by
    calc
      value a * value b =
          (a.lo.toNat + Challenge.EvmProof.Limbs.radix * a.hi.toNat) *
            (b.lo.toNat + Challenge.EvmProof.Limbs.radix * b.hi.toNat) := rfl
      _ = a.lo.toNat * b.lo.toNat + Challenge.EvmProof.Limbs.radix *
            (a.hi.toNat * b.lo.toNat + a.lo.toNat * b.hi.toNat) +
          Challenge.EvmProof.Limbs.radix ^ 2 *
            (a.hi.toNat * b.hi.toNat) := by ring
      _ = p00.lo.toNat + Challenge.EvmProof.Limbs.radix * middle.word.toNat +
          Challenge.EvmProof.Limbs.radix ^ 2 * topNat := by
        unfold topNat
        nlinarith [h00, h10, h01, hmiddle]
  have hpSq : p ^ 2 < Challenge.EvmProof.Limbs.radix ^ 3 := by
    norm_num [p, absU, Challenge.EvmProof.Limbs.radix]
  have hproduct : value a * value b < p ^ 2 := by
    simpa [pow_two] using Nat.mul_lt_mul_of_lt_of_lt ha.2 hb.2
  have htop : topNat < Challenge.EvmProof.Limbs.radix := by
    rw [hreconstruct] at hproduct
    nlinarith [hproduct.trans hpSq]
  change topNat < Challenge.EvmProof.Limbs.radix
  exact htop

theorem schoolbookProduct_r2_value {a b : Limbs}
    (ha : Canonical a) (hb : Canonical b) :
    (schoolbookProduct a b).r2.toNat = schoolbookTop a b := by
  let p00 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.lo
  let p10 := Challenge.EvmProof.Limbs.fullMul256 a.hi b.lo
  let p01 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.hi
  let middle := Challenge.EvmProof.Limbs.addThree256 p00.hi p10.lo p01.lo
  have htop := schoolbookTop_lt ha hb
  change p10.hi.toNat + p01.hi.toNat + a.hi.toNat * b.hi.toNat +
    middle.carry.toNat < Challenge.EvmProof.Limbs.radix at htop
  have hmidBound : a.hi.toNat * b.hi.toNat <
      Challenge.EvmProof.Limbs.radix := by omega
  have hmid : (a.hi * b.hi).toNat = a.hi.toNat * b.hi.toNat := by
    change (a.hi.val * b.hi.val).val = _
    rw [Fin.val_mul]
    exact Nat.mod_eq_of_lt hmidBound
  have hleft : p10.hi.toNat + p01.hi.toNat <
      Challenge.EvmProof.Limbs.radix := by omega
  have hright : a.hi.toNat * b.hi.toNat + middle.carry.toNat <
      Challenge.EvmProof.Limbs.radix := by omega
  change (p10.hi + p01.hi + (a.hi * b.hi + middle.carry)).toNat =
    schoolbookTop a b
  simp only [Challenge.EvmProof.Word.word_toNat_add]
  rw [hmid, show 2 ^ 256 = Challenge.EvmProof.Limbs.radix by rfl]
  rw [Nat.mod_eq_of_lt hright, Nat.mod_eq_of_lt hleft]
  have htop' : p10.hi.toNat + p01.hi.toNat +
      (a.hi.toNat * b.hi.toNat + middle.carry.toNat) <
        Challenge.EvmProof.Limbs.radix := by omega
  rw [Nat.mod_eq_of_lt htop']
  simp [schoolbookTop, p00, p10, p01, middle, Nat.add_assoc]

theorem schoolbookProduct_r2_lt {a b : Limbs}
    (ha : Canonical a) (hb : Canonical b) :
    (schoolbookProduct a b).r2.toNat < Challenge.EvmProof.Limbs.radix := by
  rw [schoolbookProduct_r2_value ha hb]
  exact schoolbookTop_lt ha hb

theorem value_schoolbookProduct {a b : Limbs}
    (ha : Canonical a) (hb : Canonical b) :
    (schoolbookProduct a b).value = value a * value b := by
  let p00 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.lo
  let p10 := Challenge.EvmProof.Limbs.fullMul256 a.hi b.lo
  let p01 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.hi
  let middle := Challenge.EvmProof.Limbs.addThree256 p00.hi p10.lo p01.lo
  have h00 := Challenge.EvmProof.Limbs.fullMul256_value a.lo b.lo
  have h10 := Challenge.EvmProof.Limbs.fullMul256_value a.hi b.lo
  have h01 := Challenge.EvmProof.Limbs.fullMul256_value a.lo b.hi
  have hmiddle := Challenge.EvmProof.Limbs.addThree256_value
    p00.hi p10.lo p01.lo
  change p00.lo.toNat + Challenge.EvmProof.Limbs.radix * p00.hi.toNat =
    a.lo.toNat * b.lo.toNat at h00
  change p10.lo.toNat + Challenge.EvmProof.Limbs.radix * p10.hi.toNat =
    a.hi.toNat * b.lo.toNat at h10
  change p01.lo.toNat + Challenge.EvmProof.Limbs.radix * p01.hi.toNat =
    a.lo.toNat * b.hi.toNat at h01
  change middle.word.toNat + Challenge.EvmProof.Limbs.radix *
    middle.carry.toNat = p00.hi.toNat + p10.lo.toNat + p01.lo.toNat at hmiddle
  have hr2 : (schoolbookProduct a b).r2.toNat = schoolbookTop a b :=
    schoolbookProduct_r2_value ha hb
  unfold SchoolbookProduct.value
  change p00.lo.toNat + Challenge.EvmProof.Limbs.radix * middle.word.toNat +
      Challenge.EvmProof.Limbs.radix ^ 2 * (schoolbookProduct a b).r2.toNat =
    value a * value b
  rw [hr2]
  unfold schoolbookTop
  change p00.lo.toNat + Challenge.EvmProof.Limbs.radix * middle.word.toNat +
      Challenge.EvmProof.Limbs.radix ^ 2 *
        (p10.hi.toNat + p01.hi.toNat + a.hi.toNat * b.hi.toNat +
          middle.carry.toNat) = value a * value b
  unfold value
  nlinarith [h00, h10, h01, hmiddle]

end Challenge.Bls12381.ProofSupport.Fp
