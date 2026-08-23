import Challenge.Bls12381.ProofSupport.PrimeCertificate.RootEvidence.Order2584487767265781317813

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate

open EvmSemantics.EVM

theorem rootOrder15778400344354997994418419698270088123916926905054652752758194827714659 :
    Precompile.modPow 2
      ((certifiedModulus - 1) /
        15778400344354997994418419698270088123916926905054652752758194827714659)
      certifiedModulus ≠ 1 := by
  bls_norm_mod_pow

end Challenge.Bls12381.ProofSupport.PrimeCertificate
