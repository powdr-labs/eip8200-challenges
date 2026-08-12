import Challenge.Bls12381.ProofSupport.PrimeCertificate.Huge

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate

open EvmSemantics.EVM
open PrimeField

theorem prime15778400344354997994418419698270088123916926905054652752758194827714659 :
    Nat.Prime
      15778400344354997994418419698270088123916926905054652752758194827714659 := by
  apply prime_of_modPow_lucas_factors
    15778400344354997994418419698270088123916926905054652752758194827714659 2
    [2, 3, 53, 475709467, 92691255082156974996979,
      1125266252156850182658904441386709967]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_three, prime53, prime475709467,
      prime92691255082156974996979,
      prime1125266252156850182658904441386709967, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

end Challenge.Bls12381.ProofSupport.PrimeCertificate
