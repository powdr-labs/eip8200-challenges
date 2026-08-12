import Challenge.Bls12381.ProofSupport.Fp2SqrtLawful
import Challenge.Bls12381.ProofSupport.MapToG2SqrtRatioDefs
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

set_option warningAsError true

/-!
# MAP_FP2_TO_G2 square-root ratio

This module refines the exact source two-attempt Fp2 square-root-ratio
schedule.  The RFC suite parameter `Z = -(2 + i)` is proved nonsquare, so a
failed first square root has a successful `Z * u / v` fallback whenever the
denominator is nonzero.
-/

namespace Challenge.Bls12381.ProofSupport.MapToG2

noncomputable local instance : Fintype Field :=
  Fintype.ofEquiv (LawfulFp2.Base × LawfulFp2.Base)
    (QuadraticAlgebra.equivProd (-1) 0).symm

private theorem five_not_square :
    ¬ IsSquare (5 : LawfulFp2.Base) := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro h5
  have hiff := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one
    (p := 5) (q := EvmSemantics.Crypto.Bls12381.p)
    (by norm_num) (by norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU])
  have hp : IsSquare
      (EvmSemantics.Crypto.Bls12381.p : ZMod 5) := hiff.mpr h5
  have hcast : (EvmSemantics.Crypto.Bls12381.p : ZMod 5) = 2 := by
    exact (ZMod.natCast_eq_natCast_iff
      EvmSemantics.Crypto.Bls12381.p 2 5).2 (by
        norm_num [Nat.ModEq, EvmSemantics.Crypto.Bls12381.p,
          EvmSemantics.Crypto.Bls12381.absU])
  rw [hcast] at hp
  revert hp
  decide

/-- The RFC G2 SSWU suite parameter is a nonsquare in the lawful Fp2 field. -/
theorem isoZ_not_isSquare : ¬ IsSquare isoZ := by
  intro hz
  apply five_not_square
  have hn := Fp2.norm_isSquare_of_isSquare hz
  have hnorm : QuadraticAlgebra.norm isoZ =
      (5 : LawfulFp2.Base) := by decide
  rwa [hnorm] at hn

private theorem nonsquare_product_square {a b : Field}
    (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) :
    IsSquare (a * b) := by
  have hane : a ≠ 0 := fun h => ha (h ▸ IsSquare.zero)
  have hbne : b ≠ 0 := fun h => hb (h ▸ IsSquare.zero)
  have hca : quadraticChar Field a = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr ha
  have hcb : quadraticChar Field b = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hb
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero hane hbne)]
  rw [map_mul, hca, hcb]
  norm_num

/-- Dividing by a nonzero denominator converts the source ratio predicate to
ordinary quadratic residuosity. -/
theorem isSquareRatio_iff_isSquare_div (u v : Field) (hv : v ≠ 0) :
    IsSquareRatio u v ↔ IsSquare (u * v⁻¹) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [← hy]
    field_simp
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [pow_two, ← hy]
    field_simp

/-- The exact source schedule satisfies the non-vacuous ratio contract for
every nonzero denominator. -/
theorem sqrtRatioSource_valid (u v : Field) (hv : v ≠ 0) :
    SqrtRatioValid u v (sqrtRatioSource u v) := by
  let quotient := u * v⁻¹
  let first := Fp2.SqrtProgram.run Fp2.lawfulSqrtOps quotient
  by_cases hfirst : first.exists_ = true
  · have hroot := Fp2.lawfulSqrtRun_success (a := quotient) hfirst
    unfold sqrtRatioSource SqrtRatioValid SswuCore.SqrtRatioValid
    dsimp only [suite]
    simp only [quotient, first, hfirst, if_true]
    rw [show first.root ^ 2 = quotient by simpa [pow_two] using hroot]
    dsimp only [quotient]
    field_simp
  · have hquotient : ¬ IsSquare quotient := by
      intro hq
      exact hfirst (Fp2.lawfulSqrtRun_complete hq)
    have hfallback : IsSquare (isoZ * quotient) :=
      nonsquare_product_square isoZ_not_isSquare hquotient
    let second := Fp2.SqrtProgram.run Fp2.lawfulSqrtOps (isoZ * quotient)
    have hsecond : second.exists_ = true :=
      Fp2.lawfulSqrtRun_complete hfallback
    have hroot := Fp2.lawfulSqrtRun_success
      (a := isoZ * quotient) hsecond
    change SqrtRatioValid u v
      (if first.exists_ then (true, first.root) else (false, second.root))
    rw [if_neg hfirst]
    unfold SqrtRatioValid SswuCore.SqrtRatioValid
    dsimp only [suite]
    simp only [Bool.false_eq_true, if_false]
    constructor
    · rw [show second.root ^ 2 = isoZ * quotient by
          simpa [second, pow_two] using hroot]
      dsimp only [quotient]
      field_simp
    · intro hsquare
      exact hquotient ((isSquareRatio_iff_isSquare_div u v hv).mp hsquare)

/-- The concrete source square-root-ratio makes projective G2 SSWU total. -/
theorem sswuSource_onCurve (u : Field) :
    ProjectiveOnCurve (sswuProjective sqrtRatioSource u) :=
  sswuProjective_onCurve sqrtRatioSource sqrtRatioSource_valid u

theorem sourceSswu_onCurve (u : Field) :
    ProjectiveOnCurve (sourceSswu u) := by
  rw [sourceSswu_eq]
  exact sswuSource_onCurve u

end Challenge.Bls12381.ProofSupport.MapToG2
