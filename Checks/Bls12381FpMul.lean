import Challenge.Bls12381.ProofSupport.FpSquare

set_option warningAsError true

namespace Checks.Bls12381FpMul

open Challenge.Bls12381.ProofSupport

example {a b : Fp.Limbs} (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.value (Fp.mulCanonical a b) =
      (Fp.value a * Fp.value b) % EvmSemantics.Crypto.Bls12381.p :=
  Fp.value_mulCanonical ha hb

example {a b : Fp.Limbs} (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.Canonical (Fp.mulCanonical a b) :=
  Fp.canonical_mulCanonical ha hb

example {a b : Fp.Limbs} (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.toField (Fp.mulCanonical a b) = Fp.toField a * Fp.toField b :=
  Fp.toField_mulCanonical ha hb

example {a b : Fp.Limbs} (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.Canonical (Fp.mulCanonical a b) ∧
      Fp.toField (Fp.mulCanonical a b) = Fp.toField a * Fp.toField b :=
  Fp.mulCanonical_spec ha hb

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    (Fp.squareSchoolbookProduct a).value = Fp.value a ^ 2 :=
  Fp.value_squareSchoolbookProduct ha

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    (Fp.squareSchoolbookProduct a).r2.toNat <
      Challenge.EvmProof.Limbs.radix :=
  Fp.squareSchoolbookProduct_r2_lt ha

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    Fp.value (Fp.squareCanonical a) =
      Fp.value a ^ 2 % EvmSemantics.Crypto.Bls12381.p :=
  Fp.value_squareCanonical ha

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    Fp.Canonical (Fp.squareCanonical a) :=
  Fp.canonical_squareCanonical ha

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    Fp.toField (Fp.squareCanonical a) = Fp.toField a ^ 2 :=
  Fp.toField_squareCanonical ha

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_mulCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_mulCanonical

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_mulCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.canonical_mulCanonical

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.refines_mulCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.refines_mulCanonical

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.toField_mulCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.toField_mulCanonical

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.mulCanonical_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.mulCanonical_spec

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.cross_double_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.cross_double_fits

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.squareSchoolbookTop_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.squareSchoolbookTop_lt

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.squareSchoolbookProduct_r2_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Fp.squareSchoolbookProduct_r2_value

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.squareSchoolbookProduct_r2_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Fp.squareSchoolbookProduct_r2_lt

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_squareSchoolbookProduct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_squareSchoolbookProduct

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_squareCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_squareCanonical

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_squareCanonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Fp.canonical_squareCanonical

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.refines_squareCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.refines_squareCanonical

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.toField_squareCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.toField_squareCanonical

end Checks.Bls12381FpMul
