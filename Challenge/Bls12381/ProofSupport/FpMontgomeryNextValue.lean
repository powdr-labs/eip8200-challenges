import Challenge.Bls12381.ProofSupport.FpMontgomeryNextBound

set_option warningAsError true

/-! # Reconstruction of the second BLS12-381 Montgomery accumulation -/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics

/-- The low product, source `ADD`, and carried high word reconstruct the
ordinary low-limb accumulation. -/
theorem montgomeryNextLow_reconstruct (state : MontgomeryState)
    (x1 : UInt256) (y : Limbs) :
    (montgomeryNextLowSum state x1 y).word.toNat +
        Challenge.EvmProof.Limbs.radix *
          (montgomeryNextCarry state x1 y).toNat =
      state.t0.toNat + x1.toNat * y.lo.toNat := by
  have hsum := Challenge.EvmProof.Limbs.addTwo256_value state.t0
    (montgomeryNextLowProduct x1 y).lo
  change (montgomeryNextLowSum state x1 y).word.toNat +
      Challenge.EvmProof.Limbs.radix *
        (montgomeryNextLowSum state x1 y).carry.toNat =
    state.t0.toNat + (montgomeryNextLowProduct x1 y).lo.toNat at hsum
  have hproduct := Challenge.EvmProof.Limbs.fullMul256_value x1 y.lo
  change (montgomeryNextLowProduct x1 y).lo.toNat +
      Challenge.EvmProof.Limbs.radix *
        (montgomeryNextLowProduct x1 y).hi.toNat =
    x1.toNat * y.lo.toNat at hproduct
  rw [montgomeryNextCarry_value]
  rw [Nat.mul_add]
  omega

/-- The exact second source product accumulation reconstructs the two low
words of the prior reduced state plus `x₁*y`.  The old `t₂` is deliberately
absent: the CIOS loop establishes it is zero before this schedule. -/
theorem montgomeryAccumulateNext_value (state : MontgomeryState)
    (x1 : UInt256) {y : Limbs} (hy : Canonical y) :
    (montgomeryAccumulateNext state x1 y).value =
      state.t0.toNat + Challenge.EvmProof.Limbs.radix * state.t1.toNat +
        x1.toNat * value y := by
  have hlow := montgomeryNextLow_reconstruct state x1 y
  have hhigh := Challenge.EvmProof.Limbs.fullMul256_value x1 y.hi
  change (montgomeryNextHighProduct x1 y).lo.toNat +
      Challenge.EvmProof.Limbs.radix *
        (montgomeryNextHighProduct x1 y).hi.toNat =
    x1.toNat * y.hi.toNat at hhigh
  have hsum1 := Challenge.EvmProof.Limbs.addTwo256_value state.t1
    (montgomeryNextHighProduct x1 y).lo
  change (montgomeryNextHighSum state x1 y).word.toNat +
      Challenge.EvmProof.Limbs.radix *
        (montgomeryNextHighSum state x1 y).carry.toNat =
    state.t1.toNat + (montgomeryNextHighProduct x1 y).lo.toNat at hsum1
  have hsum2 := Challenge.EvmProof.Limbs.addTwo256_value
    (montgomeryNextHighSum state x1 y).word
    (montgomeryNextCarry state x1 y)
  change (montgomeryNextShiftedSum state x1 y).word.toNat +
      Challenge.EvmProof.Limbs.radix *
        (montgomeryNextShiftedSum state x1 y).carry.toNat =
    (montgomeryNextHighSum state x1 y).word.toNat +
      (montgomeryNextCarry state x1 y).toNat at hsum2
  have hreconstruct := Challenge.EvmProof.Limbs.ciosAccumulate_reconstruct
    (base := Challenge.EvmProof.Limbs.radix)
    (t0 := state.t0.toNat) (t1 := state.t1.toNat)
    (m := x1.toNat) (n0 := y.lo.toNat) (n1 := y.hi.toNat)
    (low0 := (montgomeryNextLowSum state x1 y).word.toNat)
    (carry := (montgomeryNextCarry state x1 y).toNat)
    (low1 := (montgomeryNextHighProduct x1 y).lo.toNat)
    (high1 := (montgomeryNextHighProduct x1 y).hi.toNat)
    (sum1 := (montgomeryNextHighSum state x1 y).word.toNat)
    (carry1 := (montgomeryNextHighSum state x1 y).carry.toNat)
    (sum2 := (montgomeryNextShiftedSum state x1 y).word.toNat)
    (carry2 := (montgomeryNextShiftedSum state x1 y).carry.toNat)
    hlow hhigh hsum1 hsum2
  have htop := montgomeryAccumulateNext_t2_value state x1 hy
  unfold MontgomeryState.value
  change (montgomeryNextLowSum state x1 y).word.toNat +
      Challenge.EvmProof.Limbs.radix *
        (montgomeryNextShiftedSum state x1 y).word.toNat +
      Challenge.EvmProof.Limbs.radix ^ 2 *
        (montgomeryAccumulateNext state x1 y).t2.toNat = _
  rw [htop]
  simpa [montgomeryNextTopNat, value, pow_two, Nat.mul_add,
    Nat.add_assoc, Nat.mul_assoc] using hreconstruct

/-- When the prior reduction has cleared `t₂`, the second accumulation adds
exactly `x₁*y` to the reconstructed state. -/
theorem montgomeryAccumulateNext_value_of_t2_zero (state : MontgomeryState)
    (x1 : UInt256) {y : Limbs} (hy : Canonical y)
    (ht2 : state.t2 = UInt256.ofNat 0) :
    (montgomeryAccumulateNext state x1 y).value =
      state.value + x1.toNat * value y := by
  rw [montgomeryAccumulateNext_value state x1 hy]
  unfold MontgomeryState.value
  rw [ht2, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.zero_mod,
    Nat.mul_zero, Nat.add_zero]

end Challenge.Bls12381.ProofSupport.Fp
