import Challenge.Bls12381.ProofSupport.PrimeCertificate.Giant

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate

open EvmSemantics.Crypto.Bls12381
open EvmSemantics.EVM

abbrev certifiedModulus : Nat :=
  4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787

theorem p_eq_certifiedModulus : p = certifiedModulus := by
  norm_num [p, absU, certifiedModulus]

theorem rootPow :
    Precompile.modPow 2 (certifiedModulus - 1) certifiedModulus = 1 := by
  bls_norm_mod_pow

end Challenge.Bls12381.ProofSupport.PrimeCertificate
