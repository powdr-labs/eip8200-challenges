import Challenge.Bls12381.ProofSupport.PrimeCertificate.Small

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate

open EvmSemantics.EVM
open PrimeField

theorem prime1686913 : Nat.Prime 1686913 := by
  apply prime_of_modPow_lucas_factors 1686913 10
    [2, 2, 2, 2, 2, 2, 2, 3, 23, 191]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_two, Nat.prime_two,
      Nat.prime_two, Nat.prime_two, Nat.prime_two, Nat.prime_three,
      prime23, prime191, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 10 ((1686913 - 1) / 2) 1686913 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, h2, h2, h2, h2, h2, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime16447 : Nat.Prime 16447 := by
  apply prime_of_modPow_lucas_factors 16447 3 [2, 3, 2741]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_three, prime2741, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime43591 : Nat.Prime 43591 := by
  apply prime_of_modPow_lucas_factors 43591 11 [2, 3, 5, 1453]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_three, prime5, prime1453, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

theorem prime927093389 : Nat.Prime 927093389 := by
  apply prime_of_modPow_lucas_factors 927093389 3 [2, 2, 13, 409, 43591]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, prime13, prime409, prime43591, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 3 ((927093389 - 1) / 2) 927093389 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

theorem prime51376543 : Nat.Prime 51376543 := by
  apply prime_of_modPow_lucas_factors 51376543 3 [2, 3, 7, 151, 8101]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_three, prime7, prime151, prime8101, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime755057 : Nat.Prime 755057 := by
  apply prime_of_modPow_lucas_factors 755057 3 [2, 2, 2, 2, 41, 1151]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_two, Nat.prime_two,
      prime41, prime1151, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 3 ((755057 - 1) / 2) 755057 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, h2, h2, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime421987 : Nat.Prime 421987 := by
  apply prime_of_modPow_lucas_factors 421987 2 [2, 3, 53, 1327]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_three, prime53, prime1327, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

theorem prime47737 : Nat.Prime 47737 := by
  apply prime_of_modPow_lucas_factors 47737 5 [2, 2, 2, 3, 3, 3, 13, 17]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_two, Nat.prime_three,
      Nat.prime_three, Nat.prime_three, prime13, prime17, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 5 ((47737 - 1) / 2) 47737 ≠ 1 := by
      bls_norm_mod_pow
    have h3 : Precompile.modPow 5 ((47737 - 1) / 3) 47737 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, h2, h3, h3, h3, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

theorem prime609743 : Nat.Prime 609743 := by
  apply prime_of_modPow_lucas_factors 609743 5 [2, 7, 97, 449]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, prime7, prime97, prime449, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

theorem prime10177 : Nat.Prime 10177 := by
  apply prime_of_modPow_lucas_factors 10177 7 [2, 2, 2, 2, 2, 2, 3, 53]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_two, Nat.prime_two,
      Nat.prime_two, Nat.prime_two, Nat.prime_three, prime53, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 7 ((10177 - 1) / 2) 10177 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, h2, h2, h2, h2, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

theorem prime859267 : Nat.Prime 859267 := by
  apply prime_of_modPow_lucas_factors 859267 2 [2, 3, 3, 47737]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_three, Nat.prime_three, prime47737, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h3 : Precompile.modPow 2 ((859267 - 1) / 3) 859267 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨by bls_norm_mod_pow, h3, h3, by bls_norm_mod_pow, by simp⟩

theorem prime52437899 : Nat.Prime 52437899 := by
  apply prime_of_modPow_lucas_factors 52437899 2 [2, 43, 609743]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, prime43, prime609743, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

end Challenge.Bls12381.ProofSupport.PrimeCertificate

