import Challenge.Bls12381.ProofSupport.FpMontgomeryReduceReconstruct

set_option warningAsError true

/-! # BLS12-381 CIOS reduction top-word bound -/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics.Crypto.Bls12381

/-- Product-form numerator reconstructed by one reduction step. -/
def montgomeryReductionNumerator (state : MontgomeryState) : Nat :=
  state.t0.toNat + Challenge.EvmProof.Limbs.radix * state.t1.toNat +
    Challenge.EvmProof.Limbs.radix * Challenge.EvmProof.Limbs.radix *
      state.t2.toNat +
    (montgomeryReductionMultiplier state).toNat * p

theorem montgomeryReduction_reconstruct_numerator (state : MontgomeryState) :
    Challenge.EvmProof.Limbs.radix * montgomeryReductionQuotient state =
      montgomeryReductionNumerator state := by
  exact montgomeryReduction_reconstruct state

/-- If the input-plus-modulus multiple fits three words, the unwrapped source
top accumulator fits one word. -/
theorem montgomeryReductionTopNat_lt (state : MontgomeryState)
    (hbound : montgomeryReductionNumerator state <
      Challenge.EvmProof.Limbs.radix *
        (Challenge.EvmProof.Limbs.radix * Challenge.EvmProof.Limbs.radix)) :
    montgomeryReductionTopNat state < Challenge.EvmProof.Limbs.radix := by
  by_contra hnot
  have htop : Challenge.EvmProof.Limbs.radix ≤
      montgomeryReductionTopNat state := Nat.le_of_not_gt hnot
  have hinner : Challenge.EvmProof.Limbs.radix *
        Challenge.EvmProof.Limbs.radix ≤
      Challenge.EvmProof.Limbs.radix * montgomeryReductionTopNat state :=
    Nat.mul_le_mul_left Challenge.EvmProof.Limbs.radix htop
  have hquotient : Challenge.EvmProof.Limbs.radix *
        Challenge.EvmProof.Limbs.radix ≤ montgomeryReductionQuotient state := by
    unfold montgomeryReductionQuotient
    exact hinner.trans (Nat.le_add_left _ _)
  have hscaled := Nat.mul_le_mul_left Challenge.EvmProof.Limbs.radix hquotient
  rw [montgomeryReduction_reconstruct_numerator] at hscaled
  exact (Nat.not_lt_of_ge hscaled) hbound

end Challenge.Bls12381.ProofSupport.Fp
