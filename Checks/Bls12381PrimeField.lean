import Challenge.Bls12381.ProofSupport.PrimeField

set_option warningAsError true

namespace Checks.Bls12381PrimeField

open Challenge.Bls12381.ProofSupport.PrimeField

example (hp : Nat.Prime EvmSemantics.Crypto.Bls12381.p)
    (a : LawfulFp) (ha : a ≠ 0) : a * a⁻¹ = 1 :=
  lawful_mul_inv_cancel hp a ha

#print axioms prime_of_lucas_factors
#print axioms natCast_modPow_eq_pow
#print axioms prime_of_modPow_lucas_factors
#print axioms lawful_mul_inv_cancel

end Checks.Bls12381PrimeField
