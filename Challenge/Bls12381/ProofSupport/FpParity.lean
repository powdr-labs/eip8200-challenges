import Challenge.Bls12381.ProofSupport.Fp

set_option warningAsError true

/-! # Decoded base-field parity -/

namespace Challenge.Bls12381.ProofSupport.Fp

/-- `Fp.sgn0` at the canonical decoded-limb boundary. The 48-byte wire
equivalence belongs to codec refinement. -/
def sgn0Value (a : Limbs) : Nat := value a % 2

theorem sgn0Value_lt_two (a : Limbs) : sgn0Value a < 2 := by
  exact Nat.mod_lt _ (by omega)

end Challenge.Bls12381.ProofSupport.Fp
