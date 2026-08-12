import Challenge.Bls12381.ProofSupport.PrimeCertificate.RootEvidence.Order11

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate

open EvmSemantics.EVM

theorem rootOrder23 :
    Precompile.modPow 2 ((certifiedModulus - 1) / 23) certifiedModulus ≠ 1 := by
  bls_norm_mod_pow

end Challenge.Bls12381.ProofSupport.PrimeCertificate
