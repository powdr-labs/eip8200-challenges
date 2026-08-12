import Challenge.Bls12381.ProofSupport.PrimeCertificate.Medium

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate

open EvmSemantics.EVM
open PrimeField

theorem prime9272813673901 : Nat.Prime 9272813673901 := by
  apply prime_of_modPow_lucas_factors 9272813673901 2
    [2, 2, 3, 5, 5, 7, 7577, 582767]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_three, prime5, prime5,
      prime7, prime7577, prime582767, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 2 ((9272813673901 - 1) / 2) 9272813673901 ≠ 1 := by
      bls_norm_mod_pow
    have h5 : Precompile.modPow 2 ((9272813673901 - 1) / 5) 9272813673901 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, by bls_norm_mod_pow, h5, h5, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime1928745244171409 : Nat.Prime 1928745244171409 := by
  apply prime_of_modPow_lucas_factors 1928745244171409 3
    [2, 2, 2, 2, 13, 9272813673901]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_two, Nat.prime_two,
      prime13, prime9272813673901, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 3
        ((1928745244171409 - 1) / 2) 1928745244171409 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, h2, h2, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime13090036741 : Nat.Prime 13090036741 := by
  apply prime_of_modPow_lucas_factors 13090036741 10
    [2, 2, 3, 5, 11, 47, 421987]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_three, prime5,
      prime11, by decide +kernel, prime421987, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 10 ((13090036741 - 1) / 2) 13090036741 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime64881703735777 : Nat.Prime 64881703735777 := by
  apply prime_of_modPow_lucas_factors 64881703735777 5
    [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 927093389]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_two, Nat.prime_two,
      Nat.prime_two, Nat.prime_three, Nat.prime_three, Nat.prime_three,
      Nat.prime_three, Nat.prime_three, Nat.prime_three, Nat.prime_three,
      prime927093389, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 5
        ((64881703735777 - 1) / 2) 64881703735777 ≠ 1 := by
      bls_norm_mod_pow
    have h3 : Precompile.modPow 5
        ((64881703735777 - 1) / 3) 64881703735777 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, h2, h2, h2, h3, h3, h3, h3, h3, h3, h3,
      by bls_norm_mod_pow, by simp⟩

theorem prime43670061551 : Nat.Prime 43670061551 := by
  apply prime_of_modPow_lucas_factors 43670061551 7 [2, 5, 5, 17, 51376543]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, prime5, prime5, prime17, prime51376543, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h5 : Precompile.modPow 7 ((43670061551 - 1) / 5) 43670061551 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨by bls_norm_mod_pow, h5, h5, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

end Challenge.Bls12381.ProofSupport.PrimeCertificate

