import Challenge.Bls12381.ProofSupport.PrimeCertificate.RootEvidence.Order52437899

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate

open EvmSemantics.EVM

theorem rootOrder2584487767265781317813 :
    Precompile.modPow 2
      ((certifiedModulus - 1) / 2584487767265781317813) certifiedModulus ≠ 1 := by
  bls_norm_mod_pow

end Challenge.Bls12381.ProofSupport.PrimeCertificate
