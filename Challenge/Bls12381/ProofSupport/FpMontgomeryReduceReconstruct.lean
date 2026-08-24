import Challenge.Bls12381.ProofSupport.FpMontgomeryReduceStep

set_option warningAsError true

/-!
# BLS12-381 CIOS reduction reconstruction

This module connects the exact source schedule to the abstract-base CIOS
identity without normalizing the concrete word radix.
-/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics
open EvmSemantics.Crypto.Bls12381

/-- Unwrapped mathematical value accumulated by the source's nested final
`ADD`s. -/
def montgomeryReductionTopNat (state : MontgomeryState) : Nat :=
  state.t2.toNat + (montgomeryReductionHighProduct state).hi.toNat +
    (montgomeryReductionHighSum state).carry.toNat +
    (montgomeryReductionShiftedSum state).carry.toNat

/-- The two-word shifted quotient before its final source word conversion. -/
def montgomeryReductionQuotient (state : MontgomeryState) : Nat :=
  (montgomeryReductionShiftedSum state).word.toNat +
    Challenge.EvmProof.Limbs.radix * montgomeryReductionTopNat state

theorem montgomeryReductionCarry_scaled (state : MontgomeryState) :
    Challenge.EvmProof.Limbs.radix *
        (montgomeryReductionCarry state).toNat =
      state.t0.toNat +
        (montgomeryReductionMultiplier state).toNat * modulusLo.toNat := by
  have hp := Challenge.EvmProof.Limbs.fullMul256_value
    (montgomeryReductionMultiplier state) modulusLo
  change (montgomeryReductionLowProduct state).lo.toNat +
      Challenge.EvmProof.Limbs.radix *
        (montgomeryReductionLowProduct state).hi.toNat =
      (montgomeryReductionMultiplier state).toNat * modulusLo.toNat at hp
  have hs := Challenge.EvmProof.Limbs.addTwo256_value state.t0
    (montgomeryReductionLowProduct state).lo
  change (montgomeryReductionLowSum state).word.toNat +
      Challenge.EvmProof.Limbs.radix *
        (montgomeryReductionLowSum state).carry.toNat =
      state.t0.toNat + (montgomeryReductionLowProduct state).lo.toNat at hs
  rw [montgomeryReductionLowSum_word_eq_zero,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.zero_mod, Nat.zero_add] at hs
  rw [montgomeryReductionCarry_value, Nat.mul_add]
  omega

/-- One exact source reduction step reconstructs the input plus the selected
multiple of the BLS modulus, divided by one word radix. -/
theorem montgomeryReduction_reconstruct (state : MontgomeryState) :
    Challenge.EvmProof.Limbs.radix * montgomeryReductionQuotient state =
      state.t0.toNat + Challenge.EvmProof.Limbs.radix * state.t1.toNat +
        Challenge.EvmProof.Limbs.radix * Challenge.EvmProof.Limbs.radix *
          state.t2.toNat +
        (montgomeryReductionMultiplier state).toNat * p := by
  have hcarry := montgomeryReductionCarry_scaled state
  have hprod := Challenge.EvmProof.Limbs.fullMul256_value
    (montgomeryReductionMultiplier state) modulusHi
  change (montgomeryReductionHighProduct state).lo.toNat +
      Challenge.EvmProof.Limbs.radix *
        (montgomeryReductionHighProduct state).hi.toNat =
      (montgomeryReductionMultiplier state).toNat * modulusHi.toNat at hprod
  have hsum1 := Challenge.EvmProof.Limbs.addTwo256_value state.t1
    (montgomeryReductionHighProduct state).lo
  change (montgomeryReductionHighSum state).word.toNat +
      Challenge.EvmProof.Limbs.radix *
        (montgomeryReductionHighSum state).carry.toNat =
      state.t1.toNat + (montgomeryReductionHighProduct state).lo.toNat at hsum1
  have hsum2 := Challenge.EvmProof.Limbs.addTwo256_value
    (montgomeryReductionHighSum state).word
    (montgomeryReductionCarry state)
  change (montgomeryReductionShiftedSum state).word.toNat +
      Challenge.EvmProof.Limbs.radix *
        (montgomeryReductionShiftedSum state).carry.toNat =
      (montgomeryReductionHighSum state).word.toNat +
        (montgomeryReductionCarry state).toNat at hsum2
  have h := Challenge.EvmProof.Limbs.ciosReduction_reconstruct
    (base := Challenge.EvmProof.Limbs.radix)
    (t0 := state.t0.toNat) (t1 := state.t1.toNat) (t2 := state.t2.toNat)
    (m := (montgomeryReductionMultiplier state).toNat)
    (n0 := modulusLo.toNat) (n1 := modulusHi.toNat)
    (carry := (montgomeryReductionCarry state).toNat)
    (low1 := (montgomeryReductionHighProduct state).lo.toNat)
    (high1 := (montgomeryReductionHighProduct state).hi.toNat)
    (sum1 := (montgomeryReductionHighSum state).word.toNat)
    (carry1 := (montgomeryReductionHighSum state).carry.toNat)
    (sum2 := (montgomeryReductionShiftedSum state).word.toNat)
    (carry2 := (montgomeryReductionShiftedSum state).carry.toNat)
    hcarry hprod hsum1 hsum2
  rw [modulus_words] at h
  exact h

end Challenge.Bls12381.ProofSupport.Fp
