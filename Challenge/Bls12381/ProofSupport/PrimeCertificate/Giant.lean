import Challenge.Bls12381.ProofSupport.PrimeCertificate.GiantEvidence.Pow
import Challenge.Bls12381.ProofSupport.PrimeCertificate.GiantEvidence.Order2
import Challenge.Bls12381.ProofSupport.PrimeCertificate.GiantEvidence.Order3
import Challenge.Bls12381.ProofSupport.PrimeCertificate.GiantEvidence.Order53
import Challenge.Bls12381.ProofSupport.PrimeCertificate.GiantEvidence.Order475709467
import Challenge.Bls12381.ProofSupport.PrimeCertificate.GiantEvidence.Order92691255082156974996979
import Challenge.Bls12381.ProofSupport.PrimeCertificate.GiantEvidence.Order1125266252156850182658904441386709967

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate
open PrimeField

theorem prime15778400344354997994418419698270088123916926905054652752758194827714659 :
    Nat.Prime giantCandidate := by
  apply prime_of_modPow_lucas_factors giantCandidate 2
    [2, 3, 53, 475709467, 92691255082156974996979,
      1125266252156850182658904441386709967]
  · norm_num [giantCandidate]
  · norm_num [giantCandidate]
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_three, prime53, prime475709467,
      prime92691255082156974996979,
      prime1125266252156850182658904441386709967, by simp⟩
  · exact giantPow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨giantOrder2, giantOrder3, giantOrder53, giantOrder475709467,
      giantOrder92691255082156974996979,
      giantOrder1125266252156850182658904441386709967, by simp⟩

end Challenge.Bls12381.ProofSupport.PrimeCertificate
