import Challenge.Bls12381.ProofSupport.FpSqrtLawful

set_option warningAsError true

namespace Checks.Bls12381FpSqrtLawful

open Challenge.Bls12381.ProofSupport

example (x : PrimeField.LawfulFp) :
    Fp.lawfulSqrt x =
      x ^ ((EvmSemantics.Crypto.Bls12381.p + 1) / 4) :=
  Fp.lawfulSqrt_eq x

example {x : PrimeField.LawfulFp} (hx : IsSquare x) :
    Fp.lawfulSqrt x ^ 2 = x :=
  Fp.lawfulSqrt_square hx

example {x : PrimeField.LawfulFp} (hx : IsSquare x) :
    IsSquare (Fp.lawfulSqrt x) :=
  Fp.lawfulSqrt_isSquare hx

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.p_mod_four' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.p_mod_four

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.lawfulSqrt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.lawfulSqrt_eq

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_sqrt_pow_square_of_isSquare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.lawful_sqrt_pow_square_of_isSquare

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.lawfulSqrt_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.lawfulSqrt_square

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.lawfulSqrt_isSquare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.lawfulSqrt_isSquare

end Checks.Bls12381FpSqrtLawful
