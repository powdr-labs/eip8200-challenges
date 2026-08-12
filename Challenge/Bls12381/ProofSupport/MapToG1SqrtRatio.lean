import Challenge.Bls12381.ProofSupport.MapToG1
import Mathlib.NumberTheory.LegendreSymbol.Basic

set_option warningAsError true

/-! # Source G1 square-root ratio -/

namespace Challenge.Bls12381.ProofSupport.MapToG1

/-- Exact source exponent `(p-3)/4`. -/
def sqrtRatioExponent : Nat :=
  (EvmSemantics.Crypto.Bls12381.p - 3) / 4

/-- The `y1` candidate computed by `Fp.sqrtRatio`: `(u*v³)^c1 * u*v`.
Irreducibility prevents the fixed 381-bit exponent from expanding through
unrelated SSWU refinements. -/
irreducible_def sqrtRatioCandidate (lemma := sqrtRatioCandidate_eq)
    (u v : Field) : Field :=
  (u * v ^ 3) ^ sqrtRatioExponent * (u * v)

/-- Source control flow, including the `sqrt(-Z)` fallback. -/
def sqrtRatioSource (u v : Field) : Bool × Field :=
  let y1 := sqrtRatioCandidate u v
  let isQr := decide (y1 ^ 2 * v = u)
  (isQr, if isQr then y1 else y1 * sqrtMinusZ)

private theorem candidate_relation_generic {F : Type} [_root_.Field F]
    (u v : F) (k half period : Nat)
    (hhalf : half = 2 * k + 1)
    (hsum : 6 * k + 3 + half = 2 * period)
    (hperiod : v ^ period = 1) :
    ((u * v ^ 3) ^ k * (u * v)) ^ 2 * v =
      u * (u * v⁻¹) ^ half := by
  have hproduct : v ^ (6 * k + 3) * v ^ half = 1 := by
    rw [← pow_add, hsum, show 2 * period = period + period by omega,
      pow_add, hperiod, one_mul]
  have hvPower : v ^ (6 * k + 3) = (v ^ half)⁻¹ :=
    eq_inv_of_mul_eq_one_left hproduct
  calc
    ((u * v ^ 3) ^ k * (u * v)) ^ 2 * v =
        (u ^ k) ^ 2 * u ^ 2 * (((v ^ 3) ^ k) ^ 2 * v ^ 3) := by
      rw [mul_pow, mul_pow, mul_pow]
      ring
    _ = u ^ (k * 2 + 2) * v ^ ((3 * k) * 2 + 3) := by
      rw [← pow_mul u k 2, ← pow_mul v 3 k, ← pow_mul v (3 * k) 2,
        ← pow_add, ← pow_add]
    _ = u ^ (2 * k + 2) * v ^ (6 * k + 3) := by
      congr 2 <;> ring
    _ = u ^ (half + 1) * (v ^ half)⁻¹ := by
      rw [hvPower]
      congr 2
      omega
    _ = u * (u * v⁻¹) ^ half := by
      rw [mul_pow, inv_pow, hhalf]
      ring

private theorem sqrtRatioCandidate_relation (u v : Field) (hv : v ≠ 0) :
    sqrtRatioCandidate u v ^ 2 * v =
      u * (u * v⁻¹) ^ (EvmSemantics.Crypto.Bls12381.p / 2) := by
  rw [sqrtRatioCandidate_eq]
  unfold sqrtRatioExponent
  apply candidate_relation_generic u v
      ((EvmSemantics.Crypto.Bls12381.p - 3) / 4)
      (EvmSemantics.Crypto.Bls12381.p / 2)
      (EvmSemantics.Crypto.Bls12381.p - 1)
  · norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU]
  · norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU]
  · exact ZMod.pow_card_sub_one_eq_one hv

private theorem ratio_ne_zero {u v : Field} (hu : u ≠ 0) (hv : v ≠ 0) :
    u * v⁻¹ ≠ 0 := mul_ne_zero hu (inv_ne_zero hv)

private theorem isSquareRatio_iff {u v : Field} (hv : v ≠ 0) :
    IsSquareRatio u v ↔ IsSquare (u * v⁻¹) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    calc
      u * v⁻¹ = (y ^ 2 * v) * v⁻¹ := by rw [hy]
      _ = y ^ 2 := by rw [mul_assoc, mul_inv_cancel₀ hv, mul_one]
      _ = y * y := pow_two y
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    calc
      y ^ 2 * v = (y * y) * v := by rw [pow_two]
      _ = (u * v⁻¹) * v := by rw [← hy]
      _ = u := by rw [mul_assoc, inv_mul_cancel₀ hv, mul_one]

/-- The exact source candidate and branch implement the non-vacuous
square-root-ratio contract for every nonzero denominator. -/
theorem sqrtRatioSource_valid (u v : Field) (hv : v ≠ 0) :
    SqrtRatioValid u v (sqrtRatioSource u v) := by
  generalize hy1Def : sqrtRatioCandidate u v = y1
  have hy1 := sqrtRatioCandidate_relation u v hv
  rw [hy1Def] at hy1
  unfold sqrtRatioSource
  rw [hy1Def]
  unfold SqrtRatioValid SswuCore.SqrtRatioValid
  dsimp only [suite]
  by_cases hcheck : y1 ^ 2 * v = u
  · simp only [hcheck, decide_true, if_true]
  · have hu : u ≠ 0 := by
      intro hu
      apply hcheck
      simpa [hu] using hy1
    let ratio := u * v⁻¹
    have hratio := ZMod.pow_div_two_eq_neg_one_or_one
      EvmSemantics.Crypto.Bls12381.p (ratio_ne_zero hu hv)
    have hratioNeg : ratio ^ (EvmSemantics.Crypto.Bls12381.p / 2) = -1 := by
      rcases hratio with hratioOne | hratioNeg
      · exfalso
        apply hcheck
        rw [hy1, hratioOne, mul_one]
      · exact hratioNeg
    have hy1Neg : y1 ^ 2 * v = -u := by
      rw [hy1, hratioNeg, mul_neg, mul_one]
    have hy2 : (y1 * sqrtMinusZ) ^ 2 * v = isoZ * u := by
      rw [mul_pow]
      calc
        (y1 ^ 2 * sqrtMinusZ ^ 2) * v =
            sqrtMinusZ ^ 2 * (y1 ^ 2 * v) := by ring
        _ = isoZ * u := by rw [sqrtMinusZ_square, hy1Neg]; ring
    have hnotSquare : ¬ IsSquareRatio u v := by
      intro hsquare
      have hratioSquare : IsSquare ratio := (isSquareRatio_iff hv).mp hsquare
      have hcriterion := (ZMod.euler_criterion
        EvmSemantics.Crypto.Bls12381.p (ratio_ne_zero hu hv)).mp hratioSquare
      rw [hratioNeg] at hcriterion
      have honeNeg : (-1 : Field) ≠ 1 := by decide
      exact honeNeg hcriterion
    simp only [hcheck, decide_false, Bool.false_eq_true, if_false, hy2,
      hnotSquare, not_false_eq_true, and_self]

end Challenge.Bls12381.ProofSupport.MapToG1
