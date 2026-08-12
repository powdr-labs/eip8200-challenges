import Challenge.Bls12381.ProofSupport.FpSqrt

set_option warningAsError true

namespace Checks.Bls12381FpSqrt

open Challenge.Bls12381.ProofSupport

example : EvmSemantics.Crypto.Bls12381.p % 4 = 3 :=
  Fp.p_mod_four

example (a : Fp.Limbs) :
    Fp.sqrtCanonical a =
      Fp.montgomeryPowDecoded a Fp.pPlus1Div4Bytes :=
  rfl

example (a : Fp.Limbs) :
    Fp.isSquareCanonical a =
      if Fp.isZeroValue a then true
      else
        let root := Fp.sqrtCanonical a
        let check := Fp.squareCanonical root
        Fp.eqCanonicalValue check a :=
  rfl

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    Fp.Canonical (Fp.sqrtCanonical a) :=
  Fp.canonical_sqrtCanonical ha

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    (Fp.value (Fp.sqrtCanonical a) : PrimeField.LawfulFp) =
      (Fp.value a : PrimeField.LawfulFp) ^
        ((EvmSemantics.Crypto.Bls12381.p + 1) / 4) :=
  Fp.lawful_sqrtCanonical_pow ha

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    (Fp.value (Fp.sqrtCanonical a) : PrimeField.LawfulFp) =
      Fp.lawfulSqrt (Fp.value a : PrimeField.LawfulFp) :=
  Fp.sqrtCanonical_refines_lawful ha

example {a : Fp.Limbs} (ha : Fp.Canonical a)
    (hzero : Fp.value a = 0) :
    (Fp.value (Fp.sqrtCanonical a) : PrimeField.LawfulFp) = 0 :=
  Fp.lawful_sqrtCanonical_zero ha hzero

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    Fp.isSquareCanonical a = true ↔
      IsSquare (Fp.value a : PrimeField.LawfulFp) :=
  Fp.isSquareCanonical_iff ha

example {a : Fp.Limbs} (ha : Fp.Canonical a)
    (hsquare : IsSquare (Fp.value a : PrimeField.LawfulFp)) :
    (Fp.value (Fp.squareCanonical (Fp.sqrtCanonical a)) :
      PrimeField.LawfulFp) = (Fp.value a : PrimeField.LawfulFp) :=
  Fp.lawful_square_sqrtCanonical ha hsquare

example {a : Fp.Limbs} (ha : Fp.Canonical a)
    (hsquare : IsSquare (Fp.value a : PrimeField.LawfulFp)) :
    Fp.squareCanonical (Fp.sqrtCanonical a) = a :=
  Fp.square_sqrtCanonical ha hsquare

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_sqrtCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.canonical_sqrtCanonical

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_sqrtCanonical_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.lawful_sqrtCanonical_pow

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.sqrtCanonical_refines_lawful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.sqrtCanonical_refines_lawful

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_sqrtCanonical_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.lawful_sqrtCanonical_zero

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.isSquareCanonical_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.isSquareCanonical_zero

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_squareCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.lawful_squareCanonical

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_square_sqrtCanonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.lawful_square_sqrtCanonical

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.square_sqrtCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.square_sqrtCanonical

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.isSquareCanonical_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.isSquareCanonical_sound

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.isSquareCanonical_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.isSquareCanonical_complete

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.isSquareCanonical_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.isSquareCanonical_iff

end Checks.Bls12381FpSqrt
