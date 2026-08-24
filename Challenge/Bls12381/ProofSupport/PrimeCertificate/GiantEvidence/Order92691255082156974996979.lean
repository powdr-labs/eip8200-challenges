import Challenge.Bls12381.ProofSupport.PrimeCertificate.GiantBase

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate
open EvmSemantics.EVM

theorem giantOrder92691255082156974996979 :
    Precompile.modPow 2 ((giantCandidate - 1) / 92691255082156974996979)
      giantCandidate ≠ 1 := by
  bls_norm_mod_pow

end Challenge.Bls12381.ProofSupport.PrimeCertificate
