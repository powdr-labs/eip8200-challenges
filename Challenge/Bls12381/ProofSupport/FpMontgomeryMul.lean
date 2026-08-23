import Challenge.Bls12381.ProofSupport.FpMontgomeryRelation
import Challenge.Bls12381.ProofSupport.FpRepresentation
import Challenge.Bls12381.ProofSupport.FpWordBridge

set_option warningAsError true

/-! # Canonical BLS12-381 `montMul2` boundary -/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics.Crypto.Bls12381

/-- Two-word Montgomery radix used by `montMul2`. -/
def montgomeryRadix : Nat :=
  Challenge.EvmProof.Limbs.radix * Challenge.EvmProof.Limbs.radix

/-- One conditional subtraction computes reduction modulo a positive modulus
when the input is below twice that modulus. -/
theorem oneConditionalSubtraction_eq_mod {n modulus : Nat}
    (hn : n < 2 * modulus) :
    (if modulus ≤ n then n - modulus else n) = n % modulus := by
  by_cases hsmall : n < modulus
  · rw [if_neg (Nat.not_le_of_lt hsmall), Nat.mod_eq_of_lt hsmall]
  · have hge : modulus ≤ n := Nat.le_of_not_gt hsmall
    have hdifference : n - modulus < modulus := by omega
    rw [if_pos hge, Nat.mod_eq_sub_mod hge,
      Nat.mod_eq_of_lt hdifference]

/-- Reinterpret the exact source output pair as a base-field limb value. -/
def montMul2 (x y : Limbs) : Limbs :=
  ofWide (montMul2Words x y)

@[simp] theorem value_montMul2_words (x y : Limbs) :
    value (montMul2 x y) = (montMul2Words x y).value := by
  exact value_ofWide _

/-- The final source correction reduces the raw CIOS result modulo `p`. -/
theorem value_montMul2 {x y : Limbs} (hx : Canonical x) (hy : Canonical y) :
    value (montMul2 x y) = (montgomeryResultWords x y).value % p := by
  rw [value_montMul2_words]
  unfold montMul2Words
  rw [montgomeryFinalCorrect_value]
  exact oneConditionalSubtraction_eq_mod
    (montgomeryResultWords_lt_two_modulus hx hy)

/-- The complete source result is a canonical base-field representation. -/
theorem canonical_montMul2 {x y : Limbs}
    (hx : Canonical x) (hy : Canonical y) :
    Canonical (montMul2 x y) := by
  have hvalue : value (montMul2 x y) < p := by
    rw [value_montMul2 hx hy]
    exact Nat.mod_lt _ (by norm_num [p, absU])
  exact canonical_of_value_lt _ hvalue

/-- The corrected source output satisfies the defining Montgomery congruence. -/
theorem montMul2_modEq {x y : Limbs}
    (hx : Canonical x) (hy : Canonical y) :
    montgomeryRadix * value (montMul2 x y) ≡ value x * value y [MOD p] := by
  have hreconstruct := montgomeryTwoStep_reconstruct x hy
  have hraw : montgomeryRadix * (montgomeryResultWords x y).value ≡
      value x * value y [MOD p] := by
    unfold Nat.ModEq
    have hmod := congrArg (fun n => n % p) hreconstruct
    simpa [montgomeryRadix, Nat.add_mod, Nat.mul_mod] using hmod
  unfold Nat.ModEq at hraw ⊢
  rw [value_montMul2 hx hy]
  calc
    (montgomeryRadix * ((montgomeryResultWords x y).value % p)) % p =
        (montgomeryRadix * (montgomeryResultWords x y).value) % p := by
      simp [Nat.mul_mod]
    _ = (value x * value y) % p := hraw

end Challenge.Bls12381.ProofSupport.Fp
