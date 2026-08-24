import Challenge.Bls12381.ProofSupport.FpMontgomeryReduceBound

set_option warningAsError true

/-! # BLS12-381 CIOS reduction source value -/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics

/-- If the unwrapped top fits one word, all three nested source top-word
`ADD`s are nonwrapping. -/
theorem montgomeryReduceStep_t1_value_of_top_lt (state : MontgomeryState)
    (htop : montgomeryReductionTopNat state <
      Challenge.EvmProof.Limbs.radix) :
    (montgomeryReduceStep state).t1.toNat =
      montgomeryReductionTopNat state := by
  unfold montgomeryReductionTopNat at htop
  have hcarries :
      (montgomeryReductionHighSum state).carry.toNat +
          (montgomeryReductionShiftedSum state).carry.toNat <
        Challenge.EvmProof.Limbs.radix := by omega
  have hhigh : (montgomeryReductionHighProduct state).hi.toNat +
        ((montgomeryReductionHighSum state).carry.toNat +
          (montgomeryReductionShiftedSum state).carry.toNat) <
      Challenge.EvmProof.Limbs.radix := by omega
  have hall : state.t2.toNat +
        ((montgomeryReductionHighProduct state).hi.toNat +
          ((montgomeryReductionHighSum state).carry.toNat +
            (montgomeryReductionShiftedSum state).carry.toNat)) <
      Challenge.EvmProof.Limbs.radix := by omega
  change (state.t2 +
      ((montgomeryReductionHighProduct state).hi +
        ((montgomeryReductionHighSum state).carry +
          (montgomeryReductionShiftedSum state).carry))).toNat =
    montgomeryReductionTopNat state
  simp only [Challenge.EvmProof.Word.word_toNat_add]
  rw [show 2 ^ 256 = Challenge.EvmProof.Limbs.radix by rfl,
    Nat.mod_eq_of_lt hcarries, Nat.mod_eq_of_lt hhigh,
    Nat.mod_eq_of_lt hall]
  simp [montgomeryReductionTopNat, Nat.add_assoc]

/-- The exact source state reconstructs the unwrapped two-word quotient when
its top accumulator fits one word. -/
theorem montgomeryReduceStep_value_of_top_lt (state : MontgomeryState)
    (htopBound : montgomeryReductionTopNat state <
      Challenge.EvmProof.Limbs.radix) :
    (montgomeryReduceStep state).value =
      montgomeryReductionQuotient state := by
  have htop := montgomeryReduceStep_t1_value_of_top_lt state htopBound
  unfold MontgomeryState.value
  change (montgomeryReductionShiftedSum state).word.toNat +
      Challenge.EvmProof.Limbs.radix *
        (montgomeryReduceStep state).t1.toNat +
      Challenge.EvmProof.Limbs.radix ^ 2 * (UInt256.ofNat 0).toNat = _
  rw [htop, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.zero_mod,
    Nat.mul_zero, Nat.add_zero]
  rfl

/-- Direct scaled refinement from a source-local top-word bound. -/
theorem montgomeryReduceStep_scaled_of_top_lt (state : MontgomeryState)
    (htop : montgomeryReductionTopNat state <
      Challenge.EvmProof.Limbs.radix) :
    Challenge.EvmProof.Limbs.radix * (montgomeryReduceStep state).value =
      montgomeryReductionNumerator state := by
  rw [montgomeryReduceStep_value_of_top_lt state htop]
  exact montgomeryReduction_reconstruct_numerator state

/-- Under the three-word numerator bound, all nested source top-word `ADD`s
are nonwrapping. -/
theorem montgomeryReduceStep_t1_value (state : MontgomeryState)
    (hbound : montgomeryReductionNumerator state <
      Challenge.EvmProof.Limbs.radix *
        (Challenge.EvmProof.Limbs.radix * Challenge.EvmProof.Limbs.radix)) :
    (montgomeryReduceStep state).t1.toNat =
      montgomeryReductionTopNat state :=
  montgomeryReduceStep_t1_value_of_top_lt state
    (montgomeryReductionTopNat_lt state hbound)

/-- The numerator-bound compatibility endpoint. -/
theorem montgomeryReduceStep_value (state : MontgomeryState)
    (hbound : montgomeryReductionNumerator state <
      Challenge.EvmProof.Limbs.radix *
        (Challenge.EvmProof.Limbs.radix * Challenge.EvmProof.Limbs.radix)) :
    (montgomeryReduceStep state).value =
      montgomeryReductionQuotient state :=
  montgomeryReduceStep_value_of_top_lt state
    (montgomeryReductionTopNat_lt state hbound)

/-- One exact source reduction divides the reconstructed numerator by one
word radix. -/
theorem montgomeryReduceStep_scaled (state : MontgomeryState)
    (hbound : montgomeryReductionNumerator state <
      Challenge.EvmProof.Limbs.radix *
        (Challenge.EvmProof.Limbs.radix * Challenge.EvmProof.Limbs.radix)) :
    Challenge.EvmProof.Limbs.radix * (montgomeryReduceStep state).value =
      montgomeryReductionNumerator state := by
  exact montgomeryReduceStep_scaled_of_top_lt state
    (montgomeryReductionTopNat_lt state hbound)

end Challenge.Bls12381.ProofSupport.Fp
