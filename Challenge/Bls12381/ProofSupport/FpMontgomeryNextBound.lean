import Challenge.Bls12381.ProofSupport.FpMontgomeryNext

set_option warningAsError true

/-! # Bounds for the second BLS12-381 Montgomery accumulation -/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics
open EvmSemantics.Crypto.Bls12381

/-- The source's `hi + lt(s,t₀)` carry in iteration `i = 1` does not wrap. -/
theorem montgomeryNextCarry_value (state : MontgomeryState) (x1 : UInt256)
    (y : Limbs) :
    (montgomeryNextCarry state x1 y).toNat =
      (montgomeryNextLowProduct x1 y).hi.toNat +
        (montgomeryNextLowSum state x1 y).carry.toNat := by
  have hhi := Challenge.EvmProof.Limbs.fullMul256_hi_lt_pred x1 y.lo
  change (montgomeryNextLowProduct x1 y).hi.toNat <
    Challenge.EvmProof.Limbs.radix - 1 at hhi
  have hcarry := Challenge.EvmProof.Limbs.addTwo256_carry_lt_two state.t0
    (montgomeryNextLowProduct x1 y).lo
  change (montgomeryNextLowSum state x1 y).carry.toNat < 2 at hcarry
  have hsum : (montgomeryNextLowProduct x1 y).hi.toNat +
      (montgomeryNextLowSum state x1 y).carry.toNat <
        Challenge.EvmProof.Limbs.radix := by omega
  unfold montgomeryNextCarry
  rw [Challenge.EvmProof.Word.word_toNat_add,
    show 2 ^ 256 = Challenge.EvmProof.Limbs.radix by rfl,
    Nat.mod_eq_of_lt hsum]

/-- Unwrapped source top accumulator for the second product accumulation. -/
def montgomeryNextTopNat (state : MontgomeryState) (x1 : UInt256)
    (y : Limbs) : Nat :=
  (montgomeryNextHighProduct x1 y).hi.toNat +
    (montgomeryNextHighSum state x1 y).carry.toNat +
      (montgomeryNextShiftedSum state x1 y).carry.toNat

/-- Small fixed certificate bounding the second accumulation's top word. -/
theorem montgomeryNextTopConstant_lt :
    modulusHi.toNat + 1 + 1 < Challenge.EvmProof.Limbs.radix := by
  norm_num [modulusHi, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Limbs.radix]

/-- The unwrapped top accumulator fits one word for a canonical multiplier. -/
theorem montgomeryNextTopNat_lt (state : MontgomeryState) (x1 : UInt256)
    {y : Limbs} (hy : Canonical y) :
    montgomeryNextTopNat state x1 y < Challenge.EvmProof.Limbs.radix := by
  have hhigh := Challenge.EvmProof.Limbs.fullMul256_hi_le_right x1 y.hi
  change (montgomeryNextHighProduct x1 y).hi.toNat ≤ y.hi.toNat at hhigh
  have hyhi := canonical_hi_le_modulusHi hy
  have hcarry1 := Challenge.EvmProof.Limbs.addTwo256_carry_lt_two state.t1
    (montgomeryNextHighProduct x1 y).lo
  change (montgomeryNextHighSum state x1 y).carry.toNat < 2 at hcarry1
  have hcarry2 := Challenge.EvmProof.Limbs.addTwo256_carry_lt_two
    (montgomeryNextHighSum state x1 y).word
    (montgomeryNextCarry state x1 y)
  change (montgomeryNextShiftedSum state x1 y).carry.toNat < 2 at hcarry2
  have hconstant := montgomeryNextTopConstant_lt
  unfold montgomeryNextTopNat
  omega

/-- The source's nested top-word `ADD`s do not wrap. -/
theorem montgomeryAccumulateNext_t2_value (state : MontgomeryState)
    (x1 : UInt256) {y : Limbs} (hy : Canonical y) :
    (montgomeryAccumulateNext state x1 y).t2.toNat =
      montgomeryNextTopNat state x1 y := by
  have htop := montgomeryNextTopNat_lt state x1 hy
  unfold montgomeryNextTopNat at htop
  have hcarries : (montgomeryNextHighSum state x1 y).carry.toNat +
      (montgomeryNextShiftedSum state x1 y).carry.toNat <
        Challenge.EvmProof.Limbs.radix := by omega
  have htop' : (montgomeryNextHighProduct x1 y).hi.toNat +
      ((montgomeryNextHighSum state x1 y).carry.toNat +
        (montgomeryNextShiftedSum state x1 y).carry.toNat) <
          Challenge.EvmProof.Limbs.radix := by
    simpa [Nat.add_assoc] using htop
  change ((montgomeryNextHighProduct x1 y).hi +
      ((montgomeryNextHighSum state x1 y).carry +
        (montgomeryNextShiftedSum state x1 y).carry)).toNat = _
  simp only [Challenge.EvmProof.Word.word_toNat_add]
  rw [show 2 ^ 256 = Challenge.EvmProof.Limbs.radix by rfl,
    Nat.mod_eq_of_lt hcarries, Nat.mod_eq_of_lt htop']
  simp [montgomeryNextTopNat, Nat.add_assoc]

end Challenge.Bls12381.ProofSupport.Fp
