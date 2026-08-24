import Challenge.Bls12381.ProofSupport.PrimeCertificate.GiantBase

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate
open EvmSemantics.EVM

theorem giantPow :
    Precompile.modPow 2 (giantCandidate - 1) giantCandidate = 1 := by
  bls_norm_mod_pow

end Challenge.Bls12381.ProofSupport.PrimeCertificate
