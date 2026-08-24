import Challenge.Bls12381.ProofSupport.FpMontgomeryReduce

set_option warningAsError true

/-!
# BLS12-381 Montgomery low-word cancellation

The modular-congruence chain is kept in its own elaboration unit.  Its proofs
use associativity and distributivity lemmas directly so the reducible
`2^256` radix is never expanded by a general ring normalizer.
-/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics

theorem montgomeryReductionProduct_modEq (state : MontgomeryState) :
    (montgomeryReductionMultiplier state).toNat * modulusLo.toNat ≡
      state.t0.toNat * (Challenge.EvmProof.Limbs.radix - 1)
        [MOD Challenge.EvmProof.Limbs.radix] := by
  calc
    (montgomeryReductionMultiplier state).toNat * modulusLo.toNat ≡
        (state.t0.toNat * montgomeryN0Inv.toNat) * modulusLo.toNat
          [MOD Challenge.EvmProof.Limbs.radix] :=
      (montgomeryReductionMultiplier_modEq state).mul_right _
    _ = state.t0.toNat *
        (montgomeryN0Inv.toNat * modulusLo.toNat) := by
      rw [Nat.mul_assoc]
    _ ≡ state.t0.toNat * (Challenge.EvmProof.Limbs.radix - 1)
          [MOD Challenge.EvmProof.Limbs.radix] := montgomeryN0Inv_modEq.mul_left _

end Challenge.Bls12381.ProofSupport.Fp
