import Challenge.Bls12381.ProofSupport.PrimeCertificate.VeryLarge

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate

open EvmSemantics.EVM
open PrimeField

theorem prime7259797099061183477 : Nat.Prime 7259797099061183477 := by
  apply prime_of_modPow_lucas_factors 7259797099061183477 2
    [2, 2, 941, 1928745244171409]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, prime941,
      prime1928745244171409, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 2
        ((7259797099061183477 - 1) / 2) 7259797099061183477 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime475709467 : Nat.Prime 475709467 := by
  apply prime_of_modPow_lucas_factors 475709467 2 [2, 3, 47, 1686913]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_three, by decide +kernel, prime1686913, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

theorem prime92691255082156974996979 : Nat.Prime 92691255082156974996979 := by
  apply prime_of_modPow_lucas_factors 92691255082156974996979 3
    [2, 3, 31, 467, 16447, 64881703735777]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_three, prime31, prime467, prime16447,
      prime64881703735777, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime1125266252156850182658904441386709967 :
    Nat.Prime 1125266252156850182658904441386709967 := by
  apply prime_of_modPow_lucas_factors 1125266252156850182658904441386709967 5
    [2, 3373, 43670061551, 3819663927398918131021]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, prime3373, prime43670061551,
      prime3819663927398918131021, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

theorem prime2584487767265781317813 : Nat.Prime 2584487767265781317813 := by
  apply prime_of_modPow_lucas_factors 2584487767265781317813 2
    [2, 2, 89, 7259797099061183477]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, prime89,
      prime7259797099061183477, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 2
        ((2584487767265781317813 - 1) / 2) 2584487767265781317813 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

end Challenge.Bls12381.ProofSupport.PrimeCertificate
