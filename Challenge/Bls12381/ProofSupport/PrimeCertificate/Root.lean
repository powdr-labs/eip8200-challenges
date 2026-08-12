import Challenge.Bls12381.ProofSupport.PrimeCertificate.RootEvidence.Order15778400344354997994418419698270088123916926905054652752758194827714659

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate

open EvmSemantics.Crypto.Bls12381
open PrimeField

theorem prime_certifiedModulus : Nat.Prime certifiedModulus := by
  apply prime_of_modPow_lucas_factors certifiedModulus 2
    [2, 3, 3, 11, 23, 47, 10177, 859267, 52437899,
      2584487767265781317813,
      15778400344354997994418419698270088123916926905054652752758194827714659]
  · norm_num [certifiedModulus]
  · norm_num [certifiedModulus]
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_three, Nat.prime_three, prime11, prime23,
      by decide +kernel, prime10177, prime859267, prime52437899,
      prime2584487767265781317813,
      prime15778400344354997994418419698270088123916926905054652752758194827714659,
      by simp⟩
  · exact rootPow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨rootOrder2, rootOrder3, rootOrder3, rootOrder11, rootOrder23,
      rootOrder47, rootOrder10177, rootOrder859267, rootOrder52437899,
      rootOrder2584487767265781317813,
      rootOrder15778400344354997994418419698270088123916926905054652752758194827714659,
      by simp⟩

/-- Kernel-checked primality of the fixed BLS12-381 base-field modulus. -/
theorem prime_p : Nat.Prime p := by
  rw [p_eq_certifiedModulus]
  exact prime_certifiedModulus

instance blsPrimeFact : Fact (Nat.Prime p) := ⟨prime_p⟩

/-- The lawful BLS field boundary exposes inverse cancellation without asking
every downstream refinement theorem to thread a primality hypothesis. -/
theorem lawful_mul_inv_cancel_p (a : LawfulFp) (ha : a ≠ 0) :
    a * a⁻¹ = 1 :=
  lawful_mul_inv_cancel prime_p a ha

end Challenge.Bls12381.ProofSupport.PrimeCertificate
