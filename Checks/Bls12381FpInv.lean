import Challenge.Bls12381.ProofSupport.FpInv

set_option warningAsError true

namespace Checks.Bls12381FpInv

open Challenge.Bls12381.ProofSupport

example (a : Fp.Limbs) :
    Fp.invCanonical a = Fp.montgomeryPowDecoded a Fp.pMinus2Bytes :=
  rfl

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    Fp.Canonical (Fp.invCanonical a) :=
  Fp.canonical_invCanonical ha

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    (Fp.value (Fp.invCanonical a) : PrimeField.LawfulFp) =
      (Fp.value a : PrimeField.LawfulFp) ^
        (EvmSemantics.Crypto.Bls12381.p - 2) :=
  Fp.lawful_invCanonical_pow ha

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    (Fp.value (Fp.invCanonical a) : PrimeField.LawfulFp) =
      (Fp.value a : PrimeField.LawfulFp)⁻¹ :=
  Fp.lawful_invCanonical ha

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    PrimeField.finEquiv (Fp.toField (Fp.invCanonical a)) =
      (PrimeField.finEquiv (Fp.toField a))⁻¹ :=
  Fp.toLawful_invCanonical ha

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_invCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.canonical_invCanonical

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_invCanonical_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.lawful_invCanonical_pow

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_pow_pMinus2_eq_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.lawful_pow_pMinus2_eq_inv

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_invCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.lawful_invCanonical

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.toLawful_invCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.toLawful_invCanonical

end Checks.Bls12381FpInv
