import Challenge.Bls12381.ProofSupport.PrimeCertificate.RootEvidence.Pow

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate

open EvmSemantics.EVM

theorem rootOrder2 :
    Precompile.modPow 2 ((certifiedModulus - 1) / 2) certifiedModulus ≠ 1 := by
  bls_norm_mod_pow

end Challenge.Bls12381.ProofSupport.PrimeCertificate
