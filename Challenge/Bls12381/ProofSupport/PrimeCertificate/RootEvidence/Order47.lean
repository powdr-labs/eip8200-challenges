import Challenge.Bls12381.ProofSupport.PrimeCertificate.RootEvidence.Order23

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate

open EvmSemantics.EVM

theorem rootOrder47 :
    Precompile.modPow 2 ((certifiedModulus - 1) / 47) certifiedModulus ≠ 1 := by
  bls_norm_mod_pow

end Challenge.Bls12381.ProofSupport.PrimeCertificate
