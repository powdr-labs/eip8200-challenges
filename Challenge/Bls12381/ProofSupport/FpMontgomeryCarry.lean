import Challenge.Bls12381.ProofSupport.FpMontgomeryLowWord

set_option warningAsError true

/-! # BLS12-381 Montgomery reduction carry -/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics

/-- The source's `hi + lt(s,t₀)` carry does not wrap. -/
theorem montgomeryReductionCarry_value (state : MontgomeryState) :
    (montgomeryReductionCarry state).toNat =
      (montgomeryReductionLowProduct state).hi.toNat +
        (montgomeryReductionLowSum state).carry.toNat := by
  have hhi := Challenge.EvmProof.Limbs.fullMul256_hi_lt_pred
    (montgomeryReductionMultiplier state) modulusLo
  change (montgomeryReductionLowProduct state).hi.toNat <
    Challenge.EvmProof.Limbs.radix - 1 at hhi
  have hcarry := Challenge.EvmProof.Limbs.addTwo256_carry_lt_two state.t0
    (montgomeryReductionLowProduct state).lo
  change (montgomeryReductionLowSum state).carry.toNat < 2 at hcarry
  have hsum : (montgomeryReductionLowProduct state).hi.toNat +
      (montgomeryReductionLowSum state).carry.toNat <
        Challenge.EvmProof.Limbs.radix := by omega
  unfold montgomeryReductionCarry
  rw [Challenge.EvmProof.Word.word_toNat_add,
    show 2 ^ 256 = Challenge.EvmProof.Limbs.radix by rfl,
    Nat.mod_eq_of_lt hsum]

end Challenge.Bls12381.ProofSupport.Fp
