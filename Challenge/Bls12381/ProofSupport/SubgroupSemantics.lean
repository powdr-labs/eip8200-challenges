import Challenge.Bls12381.ProofSupport.Subgroup
import Challenge.Bls12381.ProofSupport.AffineGroupBls
import Challenge.Bls12381.ProofSupport.ScalarMulSemantics

set_option warningAsError true

/-!
# Independent semantics of the local subgroup predicates

This proof-only module characterizes the executable lawful-affine checks as
annihilation by the BLS prime subgroup order in Mathlib's independent affine
groups.  It does not claim equality to the pinned opaque-inverse predicates.
-/

namespace Challenge.Bls12381.ProofSupport.SubgroupSemantics

open EvmSemantics.Crypto.Bls12381

abbrev G1ValidPoint := AffineGroup.Point G1Affine.curve
abbrev G2ValidPoint := AffineGroup.Point G2Affine.curve

theorem g1Affine_eq_true_iff_nsmul_zero (point : G1ValidPoint) :
    Subgroup.g1Affine point.1 = true ↔
      N • AffineGroup.toMathlib G1Affine.curve point = 0 := by
  constructor
  · intro hsubgroup
    have hpoint := (Subgroup.g1Affine_eq_true_iff point.1).1 hsubgroup
    have hscalar := ScalarMul.g1_nsmul N point.1 point.2
    have hlifted :
        (⟨ScalarMul.g1 N point.1,
          ScalarMul.g1_onCurve N point.1 point.2⟩ : G1ValidPoint) =
          AffineGroup.infinity G1Affine.curve := by
      apply Subtype.ext
      exact hpoint
    calc
      N • AffineGroup.toMathlib G1Affine.curve point =
          AffineGroup.toMathlib G1Affine.curve
            ⟨ScalarMul.g1 N point.1,
              ScalarMul.g1_onCurve N point.1 point.2⟩ := hscalar.symm
      _ = AffineGroup.toMathlib G1Affine.curve
          (AffineGroup.infinity G1Affine.curve) := congrArg _ hlifted
      _ = 0 := AffineGroup.toMathlib_infinity G1Affine.curve
  · intro hnsmul
    apply (Subgroup.g1Affine_eq_true_iff point.1).2
    have hscalar := ScalarMul.g1_nsmul N point.1 point.2
    have heq : AffineGroup.toMathlib G1Affine.curve
          ⟨ScalarMul.g1 N point.1,
            ScalarMul.g1_onCurve N point.1 point.2⟩ =
        AffineGroup.toMathlib G1Affine.curve
          (AffineGroup.infinity G1Affine.curve) := by
      rw [hscalar, hnsmul]
      exact (AffineGroup.toMathlib_infinity G1Affine.curve).symm
    have hlifted := AffineGroup.toMathlib_injective G1Affine.curve heq
    exact congrArg Subtype.val hlifted

theorem g2Affine_eq_true_iff_nsmul_zero (point : G2ValidPoint) :
    Subgroup.g2Affine point.1 = true ↔
      N • AffineGroup.toMathlib G2Affine.curve point = 0 := by
  constructor
  · intro hsubgroup
    have hpoint := (Subgroup.g2Affine_eq_true_iff point.1).1 hsubgroup
    have hscalar := ScalarMul.g2_nsmul N point.1 point.2
    have hlifted :
        (⟨ScalarMul.g2 N point.1,
          ScalarMul.g2_onCurve N point.1 point.2⟩ : G2ValidPoint) =
          AffineGroup.infinity G2Affine.curve := by
      apply Subtype.ext
      exact hpoint
    calc
      N • AffineGroup.toMathlib G2Affine.curve point =
          AffineGroup.toMathlib G2Affine.curve
            ⟨ScalarMul.g2 N point.1,
              ScalarMul.g2_onCurve N point.1 point.2⟩ := hscalar.symm
      _ = AffineGroup.toMathlib G2Affine.curve
          (AffineGroup.infinity G2Affine.curve) := congrArg _ hlifted
      _ = 0 := AffineGroup.toMathlib_infinity G2Affine.curve
  · intro hnsmul
    apply (Subgroup.g2Affine_eq_true_iff point.1).2
    have hscalar := ScalarMul.g2_nsmul N point.1 point.2
    have heq : AffineGroup.toMathlib G2Affine.curve
          ⟨ScalarMul.g2 N point.1,
            ScalarMul.g2_onCurve N point.1 point.2⟩ =
        AffineGroup.toMathlib G2Affine.curve
          (AffineGroup.infinity G2Affine.curve) := by
      rw [hscalar, hnsmul]
      exact (AffineGroup.toMathlib_infinity G2Affine.curve).symm
    have hlifted := AffineGroup.toMathlib_injective G2Affine.curve heq
    exact congrArg Subtype.val hlifted

def g1PointOfWire (point : Point) (hvalid : Codec.ValidG1 point) :
    G1ValidPoint := by
  refine ⟨G1Affine.ofWire point, ?_⟩
  cases point with
  | infinity => exact LawfulAffine.onCurve_infinity G1Affine.curve
  | affine x y => exact G1Affine.onCurve_ofWire hvalid

def g2PointOfWire (point : G2Point) (hvalid : Codec.ValidG2 point) :
    G2ValidPoint := by
  refine ⟨G2Affine.ofWire point, ?_⟩
  cases point with
  | infinity => exact LawfulAffine.onCurve_infinity G2Affine.curve
  | affine x y => exact G2Affine.onCurve_ofWire hvalid

theorem g1_eq_true_iff_nsmul_zero (point : Point)
    (hvalid : Codec.ValidG1 point) :
    Subgroup.g1 point = true ↔
      N • AffineGroup.toMathlib G1Affine.curve
        (g1PointOfWire point hvalid) = 0 := by
  exact g1Affine_eq_true_iff_nsmul_zero (g1PointOfWire point hvalid)

theorem g2_eq_true_iff_nsmul_zero (point : G2Point)
    (hvalid : Codec.ValidG2 point) :
    Subgroup.g2 point = true ↔
      N • AffineGroup.toMathlib G2Affine.curve
        (g2PointOfWire point hvalid) = 0 := by
  exact g2Affine_eq_true_iff_nsmul_zero (g2PointOfWire point hvalid)

end Challenge.Bls12381.ProofSupport.SubgroupSemantics
