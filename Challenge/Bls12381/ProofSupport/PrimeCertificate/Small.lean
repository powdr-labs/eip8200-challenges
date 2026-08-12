import Challenge.Bls12381.ProofSupport.PrimeCertificate.Support

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate

open EvmSemantics.EVM
open PrimeField

theorem prime3373 : Nat.Prime 3373 := by
  apply prime_of_modPow_lucas_factors 3373 5 [2, 2, 3, 281]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_three, prime281, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 5 ((3373 - 1) / 2) 3373 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime1453 : Nat.Prime 1453 := by
  apply prime_of_modPow_lucas_factors 1453 2 [2, 2, 3, 11, 11]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_three, prime11,
      prime11, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 2 ((1453 - 1) / 2) 1453 ≠ 1 := by
      bls_norm_mod_pow
    have h11 : Precompile.modPow 2 ((1453 - 1) / 11) 1453 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, by bls_norm_mod_pow, h11, h11, by simp⟩

theorem prime1327 : Nat.Prime 1327 := by
  apply prime_of_modPow_lucas_factors 1327 3 [2, 3, 13, 17]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_three, prime13, prime17, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

theorem prime2741 : Nat.Prime 2741 := by
  apply prime_of_modPow_lucas_factors 2741 2 [2, 2, 5, 137]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, prime5, prime137, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 2 ((2741 - 1) / 2) 2741 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime7577 : Nat.Prime 7577 := by
  apply prime_of_modPow_lucas_factors 7577 3 [2, 2, 2, 947]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_two, prime947, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 3 ((7577 - 1) / 2) 7577 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, h2, by bls_norm_mod_pow, by simp⟩

theorem prime582767 : Nat.Prime 582767 := by
  apply prime_of_modPow_lucas_factors 582767 5 [2, 67, 4349]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, prime67, prime4349, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime8101 : Nat.Prime 8101 := by
  apply prime_of_modPow_lucas_factors 8101 6 [2, 2, 3, 3, 3, 3, 5, 5]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_three, Nat.prime_three,
      Nat.prime_three, Nat.prime_three, prime5, prime5, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 6 ((8101 - 1) / 2) 8101 ≠ 1 := by
      bls_norm_mod_pow
    have h3 : Precompile.modPow 6 ((8101 - 1) / 3) 8101 ≠ 1 := by
      bls_norm_mod_pow
    have h5 : Precompile.modPow 6 ((8101 - 1) / 5) 8101 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, h3, h3, h3, h3, h5, h5, by simp⟩

theorem prime1151 : Nat.Prime 1151 := by
  apply prime_of_modPow_lucas_factors 1151 17 [2, 5, 5, 23]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, prime5, prime5, prime23, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h5 : Precompile.modPow 17 ((1151 - 1) / 5) 1151 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨by bls_norm_mod_pow, h5, h5, by bls_norm_mod_pow, by simp⟩

end Challenge.Bls12381.ProofSupport.PrimeCertificate

