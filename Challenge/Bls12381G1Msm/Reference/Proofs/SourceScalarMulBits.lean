import Challenge.Bls12381G1Msm.Reference.Proofs.SourceScalarMulReady

set_option warningAsError true

/-! Small arithmetic interface for the frozen most-significant-bit schedule. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def scalarMulBit (n : Nat) : U256 := BitVec.ofNat 256 (2 ^ n)

theorem scalarMulInitialBit_eq : scalarMulInitialBit = scalarMulBit 255 := by
  rfl

theorem scalarMulNextBit_succ (n : Nat) (hn : n < 255) :
    scalarMulNextBit (scalarMulBit (n + 1)) = scalarMulBit n := by
  apply BitVec.eq_of_toNat_eq
  simp only [scalarMulNextBit, BitVec.toNat_ushiftRight, scalarMulBit,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by
    have : 2 ^ (n + 1) < 2 ^ 256 := Nat.pow_lt_pow_right (by omega) (by omega)
    simpa using this),
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))]
  rw [Nat.shiftRight_eq_div_pow, pow_one, pow_succ]
  exact Nat.mul_div_left (2 ^ n) (by omega)

theorem scalarMulBit_ne_zero (n : Nat) (hn : n < 256) :
    scalarMulBit n ≠ 0 := by
  intro hzero
  have hnat := congrArg BitVec.toNat hzero
  simp only [scalarMulBit, BitVec.toNat_ofNat] at hnat
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hn)] at hnat
  exact (Nat.ne_of_gt (Nat.two_pow_pos n)) hnat

theorem scalarMulNextBit_zero : scalarMulNextBit (scalarMulBit 0) = 0 := by
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
