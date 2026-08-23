import Challenge.Bls12381.ProofSupport.FpMontgomery

set_option warningAsError true

/-!
# BLS12-381 source-specific Montgomery reduction

The CIOS reduction is separated from the initial product accumulation so its
kernel proof terms stay bounded and downstream users can reuse the compiled
stage boundary.
-/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics

/-! ## Low-word cancellation in each CIOS reduction -/

/-- Exact source `MUL(t₀, n0Inv)` used to select the reduction multiple. -/
def montgomeryReductionMultiplier (state : MontgomeryState) : UInt256 :=
  state.t0 * montgomeryN0Inv

/-- Full product of the selected reduction word and the low modulus word. -/
def montgomeryReductionLowProduct (state : MontgomeryState) :
    Challenge.EvmProof.Limbs.WideProduct :=
  Challenge.EvmProof.Limbs.fullMul256
    (montgomeryReductionMultiplier state) modulusLo

/-- Exact source `s := add(t₀, lo)` and `lt(s, t₀)` pair. -/
def montgomeryReductionLowSum (state : MontgomeryState) :
    Challenge.EvmProof.Limbs.WordSum :=
  Challenge.EvmProof.Limbs.addTwo256 state.t0
    (montgomeryReductionLowProduct state).lo

/-- Exact source `carry := add(hi, lt(s, t₀))`. -/
def montgomeryReductionCarry (state : MontgomeryState) : UInt256 :=
  (montgomeryReductionLowProduct state).hi +
    (montgomeryReductionLowSum state).carry

theorem montgomeryReductionMultiplier_value (state : MontgomeryState) :
    (montgomeryReductionMultiplier state).toNat =
      (state.t0.toNat * montgomeryN0Inv.toNat) %
        Challenge.EvmProof.Limbs.radix := by
  unfold montgomeryReductionMultiplier
  rw [Challenge.EvmProof.Word.word_toNat_mul]
  rfl

theorem montgomeryReductionLowProduct_lo_value (state : MontgomeryState) :
    (montgomeryReductionLowProduct state).lo.toNat =
      ((montgomeryReductionMultiplier state).toNat * modulusLo.toNat) %
        Challenge.EvmProof.Limbs.radix := by
  change ((montgomeryReductionMultiplier state) * modulusLo).toNat = _
  rw [Challenge.EvmProof.Word.word_toNat_mul]
  rfl

theorem montgomeryReductionMultiplier_modEq (state : MontgomeryState) :
    (montgomeryReductionMultiplier state).toNat ≡
      state.t0.toNat * montgomeryN0Inv.toNat
        [MOD Challenge.EvmProof.Limbs.radix] := by
  show (montgomeryReductionMultiplier state).toNat %
      Challenge.EvmProof.Limbs.radix =
    (state.t0.toNat * montgomeryN0Inv.toNat) %
      Challenge.EvmProof.Limbs.radix
  rw [montgomeryReductionMultiplier_value, Nat.mod_mod]

theorem montgomeryN0Inv_modEq :
    montgomeryN0Inv.toNat * modulusLo.toNat ≡
      Challenge.EvmProof.Limbs.radix - 1
        [MOD Challenge.EvmProof.Limbs.radix] := by
  show (montgomeryN0Inv.toNat * modulusLo.toNat) %
      Challenge.EvmProof.Limbs.radix =
    (Challenge.EvmProof.Limbs.radix - 1) %
      Challenge.EvmProof.Limbs.radix
  rw [montgomeryN0Inv_spec, Nat.mod_eq_of_lt (by
    exact Nat.sub_lt Challenge.EvmProof.Limbs.radix_pos (by omega))]

end Challenge.Bls12381.ProofSupport.Fp
