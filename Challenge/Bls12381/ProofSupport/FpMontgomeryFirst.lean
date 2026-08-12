import Challenge.Bls12381.ProofSupport.FpMontgomeryReduceValue

set_option warningAsError true

/-! # First BLS12-381 CIOS Montgomery iteration -/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics
open EvmSemantics.Crypto.Bls12381

/-- Canonical base-field values cannot have a high word above the high modulus
word. -/
theorem canonical_hi_le_modulusHi {y : Limbs} (hy : Canonical y) :
    y.hi.toNat ≤ modulusHi.toNat := by
  by_contra hnot
  have hnext : modulusHi.toNat + 1 ≤ y.hi.toNat := by omega
  have hscaled := Nat.mul_le_mul_left Challenge.EvmProof.Limbs.radix hnext
  have hpUpper : p < Challenge.EvmProof.Limbs.radix *
      (modulusHi.toNat + 1) := by
    calc
      p = modulusLo.toNat +
          Challenge.EvmProof.Limbs.radix * modulusHi.toNat := modulus_words.symm
      _ < Challenge.EvmProof.Limbs.radix +
          Challenge.EvmProof.Limbs.radix * modulusHi.toNat :=
        Nat.add_lt_add_right modulusLo.val.isLt _
      _ = Challenge.EvmProof.Limbs.radix * (modulusHi.toNat + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
  have hyLower : Challenge.EvmProof.Limbs.radix *
      (modulusHi.toNat + 1) ≤ value y := by
    calc
      Challenge.EvmProof.Limbs.radix * (modulusHi.toNat + 1) ≤
          Challenge.EvmProof.Limbs.radix * y.hi.toNat := hscaled
      _ ≤ y.lo.toNat + Challenge.EvmProof.Limbs.radix * y.hi.toNat :=
        Nat.le_add_left _ _
      _ = value y := rfl
  exact (Nat.not_lt_of_ge hyLower) (hy.2.trans hpUpper)

theorem montgomeryInitial_t2_le (x0 : UInt256) (y0 y1 : UInt256) :
    (montgomeryAccumulateZero x0 y0 y1).t2.toNat ≤ y1.toNat + 1 := by
  rw [montgomeryAccumulateZero_top_value]
  change (Challenge.EvmProof.Limbs.fullMul256 x0 y1).hi.toNat +
      (Challenge.EvmProof.Limbs.addTwo256
        (Challenge.EvmProof.Limbs.fullMul256 x0 y1).lo
        (Challenge.EvmProof.Limbs.fullMul256 x0 y0).hi).carry.toNat ≤
    y1.toNat + 1
  have hhigh := Challenge.EvmProof.Limbs.fullMul256_hi_le_right x0 y1
  have hcarry := Challenge.EvmProof.Limbs.addTwo256_carry_lt_two
    (Challenge.EvmProof.Limbs.fullMul256 x0 y1).lo
    (Challenge.EvmProof.Limbs.fullMul256 x0 y0).hi
  omega

/-- Small concrete certificate used by the source-local top bound. -/
theorem montgomeryTopConstant_lt :
    (modulusHi.toNat + 1) + modulusHi.toNat + 1 + 1 <
      Challenge.EvmProof.Limbs.radix := by
  norm_num [modulusHi, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Limbs.radix]

/-- The first reduction's top word fits because only high-modulus-word terms
and two one-bit carries contribute to it. -/
theorem montgomeryFirstTop_lt (x0 : UInt256) {y : Limbs}
    (hy : Canonical y) :
    montgomeryReductionTopNat (montgomeryAccumulateZero x0 y.lo y.hi) <
      Challenge.EvmProof.Limbs.radix := by
  let state := montgomeryAccumulateZero x0 y.lo y.hi
  have ht2 := montgomeryInitial_t2_le x0 y.lo y.hi
  change state.t2.toNat ≤ y.hi.toNat + 1 at ht2
  have hyhi := canonical_hi_le_modulusHi hy
  have hhigh := Challenge.EvmProof.Limbs.fullMul256_hi_le_right
    (montgomeryReductionMultiplier state) modulusHi
  change (montgomeryReductionHighProduct state).hi.toNat ≤
    modulusHi.toNat at hhigh
  have hcarry1 := Challenge.EvmProof.Limbs.addTwo256_carry_lt_two
    state.t1 (montgomeryReductionHighProduct state).lo
  change (montgomeryReductionHighSum state).carry.toNat < 2 at hcarry1
  have hcarry2 := Challenge.EvmProof.Limbs.addTwo256_carry_lt_two
    (montgomeryReductionHighSum state).word (montgomeryReductionCarry state)
  change (montgomeryReductionShiftedSum state).carry.toNat < 2 at hcarry2
  have hconstant := montgomeryTopConstant_lt
  unfold montgomeryReductionTopNat
  change state.t2.toNat + (montgomeryReductionHighProduct state).hi.toNat +
      (montgomeryReductionHighSum state).carry.toNat +
        (montgomeryReductionShiftedSum state).carry.toNat < _
  omega

/-- First exact source CIOS reduction, after processing `x₀`. -/
def montgomeryFirstReduce (x0 : UInt256) (y : Limbs) : MontgomeryState :=
  montgomeryReduceStep (montgomeryAccumulateZero x0 y.lo y.hi)

theorem montgomeryFirstReduce_scaled (x0 : UInt256) {y : Limbs}
    (hy : Canonical y) :
    Challenge.EvmProof.Limbs.radix * (montgomeryFirstReduce x0 y).value =
      montgomeryReductionNumerator
        (montgomeryAccumulateZero x0 y.lo y.hi) := by
  exact montgomeryReduceStep_scaled_of_top_lt _ (montgomeryFirstTop_lt x0 hy)

end Challenge.Bls12381.ProofSupport.Fp
