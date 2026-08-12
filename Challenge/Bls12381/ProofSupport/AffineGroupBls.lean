import Challenge.Bls12381.ProofSupport.AffineGroup
import Challenge.Bls12381.ProofSupport.G1Affine
import Challenge.Bls12381.ProofSupport.G2Affine

set_option warningAsError true

/-!
# BLS12-381 instances of the independent affine group semantics

This proof-only module keeps Mathlib's algebraic-geometry group model out of
the executable G1 and G2 affine formula modules.
-/

namespace Challenge.Bls12381.ProofSupport.AffineGroupBls

open EvmSemantics.Crypto.Bls12381

theorem g1MathCurve_discriminant_ne_zero :
    (AffineGroup.mathCurve G1Affine.curve).toAffine.Δ ≠ 0 := by
  rw [AffineGroup.mathCurve_discriminant]
  change (-6912 : G1Affine.Field) ≠ 0
  intro hzero
  have hpositive : (6912 : G1Affine.Field) = 0 := neg_eq_zero.mp hzero
  have hdiv : p ∣ 6912 :=
    (CharP.cast_eq_zero_iff G1Affine.Field p 6912).mp hpositive
  norm_num [p, absU] at hdiv

noncomputable instance g1MathCurveIsElliptic :
    WeierstrassCurve.IsElliptic (AffineGroup.mathCurve G1Affine.curve) :=
  ⟨isUnit_iff_ne_zero.mpr g1MathCurve_discriminant_ne_zero⟩

theorem g2MathCurve_discriminant_ne_zero :
    (AffineGroup.mathCurve G2Affine.curve).toAffine.Δ ≠ 0 := by
  have hconstant : (-432 : G2Affine.Field) ≠ 0 := by
    intro hzero
    have hbase : (-432 : LawfulFp2.Base) = 0 := by
      have hre := congrArg QuadraticAlgebra.re hzero
      simpa only [QuadraticAlgebra.re_neg, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.re_zero] using hre
    have hpositive : (432 : LawfulFp2.Base) = 0 := neg_eq_zero.mp hbase
    have hdiv : p ∣ 432 :=
      (CharP.cast_eq_zero_iff LawfulFp2.Base p 432).mp hpositive
    norm_num [p, absU] at hdiv
  have hb : G2Affine.curve.b ≠ 0 := by
    intro hzero
    have hbase : (4 : LawfulFp2.Base) = 0 := by
      have hre := congrArg QuadraticAlgebra.re hzero
      simp [G2Affine.curve, LawfulFp2.ofWire,
        EvmSemantics.Crypto.Bls12381.g2TwistB] at hre
    have hdiv : p ∣ 4 :=
      (CharP.cast_eq_zero_iff LawfulFp2.Base p 4).mp hbase
    norm_num [p, absU] at hdiv
  rw [AffineGroup.mathCurve_discriminant]
  convert mul_ne_zero hconstant (pow_ne_zero 2 hb) using 1
  simp [G2Affine.curve]
  ring

noncomputable instance g2MathCurveIsElliptic :
    WeierstrassCurve.IsElliptic (AffineGroup.mathCurve G2Affine.curve) :=
  ⟨isUnit_iff_ne_zero.mpr g2MathCurve_discriminant_ne_zero⟩

end Challenge.Bls12381.ProofSupport.AffineGroupBls
