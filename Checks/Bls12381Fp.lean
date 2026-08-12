import Challenge.Bls12381.ProofSupport.FpSchoolbook

set_option warningAsError true

namespace Checks.Bls12381Fp

open EvmSemantics.Crypto.Bls12381
open Challenge.Bls12381.ProofSupport

example (n : Nat) : Fp.Canonical (Fp.normalize n) :=
  Fp.canonical_normalize n

example (a b : Fp.Limbs) (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.value (Fp.addCanonical a b) = (Fp.value a + Fp.value b) % p :=
  Fp.value_addCanonical ha hb

example (a b : Fp.Limbs) (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.value (Fp.subCanonical a b) = (p + Fp.value a - Fp.value b) % p :=
  Fp.value_subCanonical ha hb

example (a b : Fp.Limbs) :
    Fp.toField (Fp.mul a b) = Fp.toField a * Fp.toField b :=
  Fp.toField_mul a b

example (a : Fp.Limbs) (exponent : Nat) :
    Fp.toField (Fp.powSpecRepr a exponent) = Fp.PowSpec a exponent :=
  Fp.toField_powSpecRepr a exponent

example (a b : Fp.Limbs) (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    (Fp.schoolbookProduct a b).value = Fp.value a * Fp.value b :=
  Fp.value_schoolbookProduct ha hb

example (a b : Fp.Limbs) (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    (Fp.schoolbookProduct a b).r2.toNat < Challenge.EvmProof.Limbs.radix :=
  Fp.schoolbookProduct_r2_lt ha hb

example (a b : Fp.Limbs) (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    (Fp.schoolbookProduct a b).r2.toNat =
      (Challenge.EvmProof.Limbs.fullMul256 a.hi b.lo).hi.toNat +
      (Challenge.EvmProof.Limbs.fullMul256 a.lo b.hi).hi.toNat +
      a.hi.toNat * b.hi.toNat +
      (Challenge.EvmProof.Limbs.addThree256
        (Challenge.EvmProof.Limbs.fullMul256 a.lo b.lo).hi
        (Challenge.EvmProof.Limbs.fullMul256 a.hi b.lo).lo
        (Challenge.EvmProof.Limbs.fullMul256 a.lo b.hi).lo).carry.toNat :=
  Fp.schoolbookProduct_r2_value ha hb

example (a b : Fp.Limbs) (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.schoolbookTop a b < Challenge.EvmProof.Limbs.radix :=
  Fp.schoolbookTop_lt ha hb

example : Fp.barrettMu = Challenge.EvmProof.Limbs.radix ^ 4 / p :=
  Fp.barrettMu_eq_floor

example : Fp.modulusLo.toNat + Challenge.EvmProof.Limbs.radix *
    Fp.modulusHi.toNat = p :=
  Fp.modulus_words

example : Fp.barrettMu = Fp.barrettMu0.toNat +
    Challenge.EvmProof.Limbs.radix * Fp.barrettMu1.toNat +
    Challenge.EvmProof.Limbs.radix ^ 2 * Fp.barrettMu2.toNat :=
  Fp.barrettMu_words

#print axioms Fp.value_addCanonical
#print axioms Fp.value_subCanonical
#print axioms Fp.toField_mul
#print axioms Fp.toField_powSpecRepr

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.schoolbookTop_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.schoolbookTop_lt

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.schoolbookProduct_r2_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.schoolbookProduct_r2_value

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.schoolbookProduct_r2_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.schoolbookProduct_r2_lt

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_schoolbookProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_schoolbookProduct

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.modulus_words' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.modulus_words

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettMu_eq_floor' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.barrettMu_eq_floor

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettMu_words' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.barrettMu_words

end Checks.Bls12381Fp
