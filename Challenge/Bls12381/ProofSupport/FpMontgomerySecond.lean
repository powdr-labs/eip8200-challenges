import Challenge.Bls12381.ProofSupport.FpMontgomeryNextValue

set_option warningAsError true

/-! # Second BLS12-381 CIOS Montgomery iteration -/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics
open EvmSemantics.Crypto.Bls12381

/-- The second product accumulation's top word is bounded by the multiplier's
high word and its two one-bit source carries. -/
theorem montgomeryAccumulateNext_t2_le (state : MontgomeryState)
    (x1 : UInt256) {y : Limbs} (hy : Canonical y) :
    (montgomeryAccumulateNext state x1 y).t2.toNat ≤ y.hi.toNat + 2 := by
  rw [montgomeryAccumulateNext_t2_value state x1 hy]
  have hhigh := Challenge.EvmProof.Limbs.fullMul256_hi_le_right x1 y.hi
  change (montgomeryNextHighProduct x1 y).hi.toNat ≤ y.hi.toNat at hhigh
  have hcarry1 := Challenge.EvmProof.Limbs.addTwo256_carry_lt_two state.t1
    (montgomeryNextHighProduct x1 y).lo
  change (montgomeryNextHighSum state x1 y).carry.toNat < 2 at hcarry1
  have hcarry2 := Challenge.EvmProof.Limbs.addTwo256_carry_lt_two
    (montgomeryNextHighSum state x1 y).word
    (montgomeryNextCarry state x1 y)
  change (montgomeryNextShiftedSum state x1 y).carry.toNat < 2 at hcarry2
  unfold montgomeryNextTopNat
  omega

/-- State after the exact second product accumulation, before its reduction. -/
def montgomerySecondAccumulate (x y : Limbs) : MontgomeryState :=
  montgomeryAccumulateNext (montgomeryFirstReduce x.lo y) x.hi y

/-- Small concrete certificate used by the second reduction's structural top
bound. -/
theorem montgomerySecondTopConstant_lt :
    (modulusHi.toNat + 2) + modulusHi.toNat + 1 + 1 <
      Challenge.EvmProof.Limbs.radix := by
  norm_num [modulusHi, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Limbs.radix]

/-- The second reduction's top word fits using only the source-local high-word
and one-bit carry bounds. -/
theorem montgomerySecondTop_lt (x : Limbs) {y : Limbs}
    (hy : Canonical y) :
    montgomeryReductionTopNat (montgomerySecondAccumulate x y) <
      Challenge.EvmProof.Limbs.radix := by
  let state := montgomerySecondAccumulate x y
  have ht2 := montgomeryAccumulateNext_t2_le
    (montgomeryFirstReduce x.lo y) x.hi hy
  change state.t2.toNat ≤ y.hi.toNat + 2 at ht2
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
  have hconstant := montgomerySecondTopConstant_lt
  unfold montgomeryReductionTopNat
  change state.t2.toNat + (montgomeryReductionHighProduct state).hi.toNat +
      (montgomeryReductionHighSum state).carry.toNat +
        (montgomeryReductionShiftedSum state).carry.toNat < _
  omega

/-- State after both exact CIOS multiply/reduce iterations. -/
def montgomerySecondReduce (x y : Limbs) : MontgomeryState :=
  montgomeryReduceStep (montgomerySecondAccumulate x y)

/-- The exact second source reduction divides its reconstructed numerator by
one word radix. -/
theorem montgomerySecondReduce_scaled (x : Limbs) {y : Limbs}
    (hy : Canonical y) :
    Challenge.EvmProof.Limbs.radix * (montgomerySecondReduce x y).value =
      montgomeryReductionNumerator (montgomerySecondAccumulate x y) := by
  exact montgomeryReduceStep_scaled_of_top_lt _ (montgomerySecondTop_lt x hy)

end Challenge.Bls12381.ProofSupport.Fp
