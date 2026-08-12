import Challenge.Bls12381.ProofSupport.PrimeCertificate.RootEvidence.Order2

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate

open EvmSemantics.EVM

theorem rootOrder3 :
    Precompile.modPow 2 ((certifiedModulus - 1) / 3) certifiedModulus ≠ 1 := by
  bls_norm_mod_pow

end Challenge.Bls12381.ProofSupport.PrimeCertificate
