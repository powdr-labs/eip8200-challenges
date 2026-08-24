import Challenge.Bls12381.ProofSupport.PrimeCertificate.RootEvidence.Order859267

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate

open EvmSemantics.EVM

theorem rootOrder52437899 :
    Precompile.modPow 2 ((certifiedModulus - 1) / 52437899) certifiedModulus ≠ 1 := by
  bls_norm_mod_pow

end Challenge.Bls12381.ProofSupport.PrimeCertificate
