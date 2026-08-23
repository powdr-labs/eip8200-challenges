import Challenge.Bls12381.ProofSupport.FpMontgomeryLowZero

set_option warningAsError true

/-!
# BLS12-381 Montgomery low-word result

This final small bridge turns the cancellation congruence into equality of the
exact wrapped EVM `ADD` result with the zero word.
-/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics

/-- The selected multiple makes the exact source low-word `ADD` equal zero. -/
theorem montgomeryReductionLowSum_word_eq_zero (state : MontgomeryState) :
    (montgomeryReductionLowSum state).word = UInt256.ofNat 0 := by
  change (Challenge.EvmProof.Limbs.addTwo256 state.t0
    (montgomeryReductionLowProduct state).lo).word = UInt256.ofNat 0
  apply Challenge.EvmProof.Limbs.addTwo256_word_eq_zero_of_modEq
  have hlo : (montgomeryReductionLowProduct state).lo.toNat ≡
      (montgomeryReductionMultiplier state).toNat * modulusLo.toNat
        [MOD Challenge.EvmProof.Limbs.radix] := by
    show (montgomeryReductionLowProduct state).lo.toNat %
        Challenge.EvmProof.Limbs.radix =
      ((montgomeryReductionMultiplier state).toNat * modulusLo.toNat) %
        Challenge.EvmProof.Limbs.radix
    rw [montgomeryReductionLowProduct_lo_value, Nat.mod_mod]
  exact ((Nat.ModEq.refl state.t0.toNat).add hlo).trans
    (montgomeryReductionCancellation_modEq state)

end Challenge.Bls12381.ProofSupport.Fp
