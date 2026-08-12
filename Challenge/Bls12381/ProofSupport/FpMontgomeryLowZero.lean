import Challenge.Bls12381.ProofSupport.FpMontgomeryCancel

set_option warningAsError true

/-!
# BLS12-381 Montgomery cancellation sum

This declaration is isolated from the product congruence so the kernel checks
each modular step independently.
-/

namespace Challenge.Bls12381.ProofSupport.Fp

theorem montgomeryReductionCancellation_modEq (state : MontgomeryState) :
    state.t0.toNat +
        (montgomeryReductionMultiplier state).toNat * modulusLo.toNat ≡ 0
      [MOD Challenge.EvmProof.Limbs.radix] := by
  calc
    state.t0.toNat +
        (montgomeryReductionMultiplier state).toNat * modulusLo.toNat ≡
      state.t0.toNat +
        state.t0.toNat * (Challenge.EvmProof.Limbs.radix - 1)
        [MOD Challenge.EvmProof.Limbs.radix] :=
      (montgomeryReductionProduct_modEq state).add_left _
    _ = state.t0.toNat * Challenge.EvmProof.Limbs.radix := by
      have hbase : 1 + (Challenge.EvmProof.Limbs.radix - 1) =
          Challenge.EvmProof.Limbs.radix :=
        Nat.add_sub_of_le (Nat.succ_le_of_lt Challenge.EvmProof.Limbs.radix_pos)
      calc
        state.t0.toNat + state.t0.toNat *
            (Challenge.EvmProof.Limbs.radix - 1) =
          state.t0.toNat * 1 + state.t0.toNat *
            (Challenge.EvmProof.Limbs.radix - 1) := by rw [Nat.mul_one]
        _ = state.t0.toNat *
            (1 + (Challenge.EvmProof.Limbs.radix - 1)) :=
          (Nat.mul_add _ _ _).symm
        _ = state.t0.toNat * Challenge.EvmProof.Limbs.radix := by rw [hbase]
    _ ≡ 0 [MOD Challenge.EvmProof.Limbs.radix] := by
      show (state.t0.toNat * Challenge.EvmProof.Limbs.radix) %
          Challenge.EvmProof.Limbs.radix =
        0 % Challenge.EvmProof.Limbs.radix
      rw [Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod]

end Challenge.Bls12381.ProofSupport.Fp
