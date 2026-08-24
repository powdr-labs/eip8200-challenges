import Challenge.Bls12381.ProofSupport.FpMontgomeryFinal

set_option warningAsError true

/-! # Algebraic relation and range of BLS12-381 `montMul2` -/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics
open EvmSemantics.Crypto.Bls12381

/-- The two one-word reduction multipliers, reconstructed as one two-word
natural. -/
def montgomeryCorrectionFactor (x y : Limbs) : Nat :=
  (montgomeryReductionMultiplier
      (montgomeryAccumulateZero x.lo y.lo y.hi)).toNat +
    Challenge.EvmProof.Limbs.radix *
      (montgomeryReductionMultiplier
        (montgomerySecondAccumulate x y)).toNat

/-- The two source reduction multipliers fit the two-word Montgomery radix. -/
theorem montgomeryCorrectionFactor_lt (x y : Limbs) :
    montgomeryCorrectionFactor x y <
      Challenge.EvmProof.Limbs.radix ^ 2 := by
  let words : Challenge.EvmProof.Limbs.WideProduct :=
    { lo := montgomeryReductionMultiplier
        (montgomeryAccumulateZero x.lo y.lo y.hi)
      hi := montgomeryReductionMultiplier (montgomerySecondAccumulate x y) }
  have hwords := Challenge.EvmProof.Limbs.WideProduct.value_lt words
  simpa [words, montgomeryCorrectionFactor,
    Challenge.EvmProof.Limbs.WideProduct.value] using hwords

@[simp] theorem montgomeryResultWords_value (x y : Limbs) :
    (montgomeryResultWords x y).value = (montgomerySecondReduce x y).value := by
  unfold montgomeryResultWords Challenge.EvmProof.Limbs.WideProduct.value
  unfold MontgomeryState.value montgomerySecondReduce montgomeryReduceStep
  simp [Challenge.EvmProof.Word.word_toNat_ofNat]

/-- Composing the two exact source reductions exposes the selected modulus
multiple and the unreduced operand product. -/
theorem montgomeryTwoStep_reconstruct (x : Limbs) {y : Limbs}
    (hy : Canonical y) :
    Challenge.EvmProof.Limbs.radix * Challenge.EvmProof.Limbs.radix *
        (montgomeryResultWords x y).value =
      value x * value y + montgomeryCorrectionFactor x y * p := by
  let firstInput := montgomeryAccumulateZero x.lo y.lo y.hi
  let first := montgomeryFirstReduce x.lo y
  let secondInput := montgomerySecondAccumulate x y
  let second := montgomerySecondReduce x y
  let m0 := (montgomeryReductionMultiplier firstInput).toNat
  let m1 := (montgomeryReductionMultiplier secondInput).toNat
  have hfirst := montgomeryFirstReduce_scaled x.lo hy
  change Challenge.EvmProof.Limbs.radix * first.value =
    montgomeryReductionNumerator firstInput at hfirst
  have hfirstValue := montgomeryAccumulateZero_value x.lo y.lo y.hi
  change firstInput.value = x.lo.toNat * value y at hfirstValue
  have hfirst' : Challenge.EvmProof.Limbs.radix * first.value =
      x.lo.toNat * value y + m0 * p := by
    rw [hfirst]
    unfold montgomeryReductionNumerator
    change firstInput.value + m0 * p = _
    rw [hfirstValue]
  have hsecond := montgomerySecondReduce_scaled x hy
  change Challenge.EvmProof.Limbs.radix * second.value =
    montgomeryReductionNumerator secondInput at hsecond
  have hsecondInput := montgomeryAccumulateNext_value
    (montgomeryFirstReduce x.lo y) x.hi hy
  change secondInput.value =
    first.t0.toNat + Challenge.EvmProof.Limbs.radix * first.t1.toNat +
      x.hi.toNat * value y at hsecondInput
  have hfirstT2 : first.t2 = UInt256.ofNat 0 := rfl
  have hfirstLow : first.t0.toNat +
      Challenge.EvmProof.Limbs.radix * first.t1.toNat = first.value := by
    unfold MontgomeryState.value
    rw [hfirstT2, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.zero_mod,
      Nat.mul_zero, Nat.add_zero]
  have hsecond' : Challenge.EvmProof.Limbs.radix * second.value =
      first.value + x.hi.toNat * value y + m1 * p := by
    rw [hsecond]
    unfold montgomeryReductionNumerator
    change secondInput.value + m1 * p = _
    rw [hsecondInput, hfirstLow]
  have hcompose := Challenge.EvmProof.Limbs.ciosTwoStep_reconstruct
    (base := Challenge.EvmProof.Limbs.radix)
    (x0 := x.lo.toNat) (x1 := x.hi.toNat) (y := value y)
    (modulus := p) (first := first.value) (second := second.value)
    (m0 := m0) (m1 := m1) hfirst' hsecond'
  rw [montgomeryResultWords_value]
  simpa [value, montgomeryCorrectionFactor, firstInput, secondInput, first,
    second, m0, m1] using hcompose

/-- Before the final conditional subtraction, the two-word result is below
`2p`; consequently one source correction is sufficient. -/
theorem montgomeryResultWords_lt_two_modulus {x y : Limbs}
    (hx : Canonical x) (hy : Canonical y) :
    (montgomeryResultWords x y).value < 2 * p := by
  let baseSq := Challenge.EvmProof.Limbs.radix *
    Challenge.EvmProof.Limbs.radix
  have hp : 0 < p := by norm_num [p, absU]
  have hbaseSq : 0 < baseSq := Nat.mul_pos
    Challenge.EvmProof.Limbs.radix_pos Challenge.EvmProof.Limbs.radix_pos
  have hproduct : value x * value y < p * p :=
    Nat.mul_lt_mul_of_lt_of_lt hx.2 hy.2
  have hpSq : p * p < baseSq * p := by
    exact (Nat.mul_lt_mul_right hp).2 (by
      simpa [baseSq, pow_two] using p_lt_radix_sq)
  have hfactor := montgomeryCorrectionFactor_lt x y
  have hfactor' : montgomeryCorrectionFactor x y < baseSq := by
    simpa [baseSq, pow_two] using hfactor
  have hmultiple : montgomeryCorrectionFactor x y * p < baseSq * p :=
    (Nat.mul_lt_mul_right hp).2 hfactor'
  have hsum : value x * value y + montgomeryCorrectionFactor x y * p <
      baseSq * (2 * p) := by
    calc
      value x * value y + montgomeryCorrectionFactor x y * p <
          baseSq * p + baseSq * p := Nat.add_lt_add
            (hproduct.trans hpSq) hmultiple
      _ = baseSq * (2 * p) := by
        rw [show 2 * p = p + p by omega, Nat.mul_add]
  have hreconstruct := montgomeryTwoStep_reconstruct x hy
  change baseSq * (montgomeryResultWords x y).value =
    value x * value y + montgomeryCorrectionFactor x y * p at hreconstruct
  rw [← hreconstruct] at hsum
  exact (Nat.mul_lt_mul_left hbaseSq).mp hsum

end Challenge.Bls12381.ProofSupport.Fp
