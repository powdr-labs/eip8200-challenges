import Challenge.Bls12381.ProofSupport.Fp

set_option warningAsError true

/-! # Shared BLS12-381 base-field representation facts -/

namespace Challenge.Bls12381.ProofSupport.Fp

/-- Any two-limb value below the BLS modulus satisfies the wire-level high
limb bound as well as the field-value bound. -/
theorem canonical_of_value_lt (a : Limbs)
    (hvalue : value a < EvmSemantics.Crypto.Bls12381.p) : Canonical a := by
  constructor
  · have hpBound : EvmSemantics.Crypto.Bls12381.p <
        Challenge.EvmProof.Limbs.radix * 2 ^ 128 := by
      norm_num [EvmSemantics.Crypto.Bls12381.p,
        EvmSemantics.Crypto.Bls12381.absU, Challenge.EvmProof.Limbs.radix]
    have hmul : Challenge.EvmProof.Limbs.radix * a.hi.toNat <
        Challenge.EvmProof.Limbs.radix * 2 ^ 128 := by
      unfold value at hvalue
      omega
    exact (Nat.mul_lt_mul_left Challenge.EvmProof.Limbs.radix_pos).mp hmul
  · exact hvalue

end Challenge.Bls12381.ProofSupport.Fp
