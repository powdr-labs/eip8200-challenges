import Challenge.Bls12381.ProofSupport.PrimeCertificate
import Mathlib.FieldTheory.Finite.Basic

set_option warningAsError true

/-!
# Lawful BLS12-381 base-field square roots

This module contains only the algebraic square-root boundary over the certified
prime field.  Concrete limbs, Montgomery exponentiation, and source constants
refine to this boundary in higher modules.
-/

namespace Challenge.Bls12381.ProofSupport.Fp

open PrimeField

theorem p_mod_four : EvmSemantics.Crypto.Bls12381.p % 4 = 3 := by
  norm_num [EvmSemantics.Crypto.Bls12381.p,
    EvmSemantics.Crypto.Bls12381.absU]

/-- The algebraic square-root candidate for a field with modulus congruent to
`3 mod 4`.  Irreducibility keeps the fixed 381-bit exponent opaque to callers.
-/
irreducible_def lawfulSqrt (lemma := lawfulSqrt_eq)
    (x : LawfulFp) : LawfulFp :=
  x ^ ((EvmSemantics.Crypto.Bls12381.p + 1) / 4)

/-- In the certified BLS field, the fixed exponent squares back every
quadratic residue, including zero. -/
theorem lawful_sqrt_pow_square_of_isSquare (x : LawfulFp)
    (hsquare : IsSquare x) :
    (x ^ ((EvmSemantics.Crypto.Bls12381.p + 1) / 4)) ^ 2 = x := by
  rcases hsquare with ⟨y, rfl⟩
  by_cases hy : y = 0
  · rw [hy]
    norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU]
  · have hexponent :
        2 * ((EvmSemantics.Crypto.Bls12381.p + 1) / 4) * 2 =
          (EvmSemantics.Crypto.Bls12381.p - 1) + 2 := by
      norm_num [EvmSemantics.Crypto.Bls12381.p,
        EvmSemantics.Crypto.Bls12381.absU]
    calc
      ((y * y) ^ ((EvmSemantics.Crypto.Bls12381.p + 1) / 4)) ^ 2 =
          y ^ (2 * ((EvmSemantics.Crypto.Bls12381.p + 1) / 4) * 2) := by
            simp only [← pow_two, ← pow_mul]
      _ = y ^ ((EvmSemantics.Crypto.Bls12381.p - 1) + 2) := by
        rw [hexponent]
      _ = y ^ (EvmSemantics.Crypto.Bls12381.p - 1) * y ^ 2 :=
        pow_add _ _ _
      _ = y * y := by
        rw [ZMod.pow_card_sub_one_eq_one hy]
        simp [pow_two]

theorem lawfulSqrt_square {x : LawfulFp} (hx : IsSquare x) :
    lawfulSqrt x ^ 2 = x := by
  rw [lawfulSqrt_eq]
  exact lawful_sqrt_pow_square_of_isSquare x hx

theorem lawfulSqrt_isSquare {x : LawfulFp} (hx : IsSquare x) :
    IsSquare (lawfulSqrt x) := by
  rcases hx with ⟨y, rfl⟩
  refine ⟨y ^ ((EvmSemantics.Crypto.Bls12381.p + 1) / 4), ?_⟩
  simp only [lawfulSqrt_eq, mul_pow]

end Challenge.Bls12381.ProofSupport.Fp
