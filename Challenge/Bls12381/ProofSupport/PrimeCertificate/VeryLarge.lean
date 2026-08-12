import Challenge.Bls12381.ProofSupport.PrimeCertificate.Large

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate

open EvmSemantics.EVM
open PrimeField

theorem prime3819663927398918131021 : Nat.Prime 3819663927398918131021 := by
  apply prime_of_modPow_lucas_factors 3819663927398918131021 6
    [2, 2, 3, 3, 5, 19, 113, 755057, 13090036741]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_three, Nat.prime_three,
      prime5, prime19, prime113, prime755057, prime13090036741, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 6
        ((3819663927398918131021 - 1) / 2) 3819663927398918131021 ≠ 1 := by
      bls_norm_mod_pow
    have h3 : Precompile.modPow 6
        ((3819663927398918131021 - 1) / 3) 3819663927398918131021 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, h3, h3, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

end Challenge.Bls12381.ProofSupport.PrimeCertificate
