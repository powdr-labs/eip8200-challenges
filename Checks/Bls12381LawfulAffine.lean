import Challenge.Bls12381.ProofSupport.LawfulAffine

set_option warningAsError true

namespace Checks.Bls12381LawfulAffine

open Challenge.Bls12381.ProofSupport.LawfulAffine

variable {F : Type} [Field F] [DecidableEq F]

example (curve : Curve F) (point : Point F) :
    add curve .infinity point = point := infinity_add curve point

example (curve : Curve F) (point : Point F) :
    add curve point .infinity = point := add_infinity curve point

example (curve : Curve F) (x y : F) :
    add curve (.affine x y) (.affine x (-y)) = .infinity :=
  add_opposite curve x y

example (curve : Curve F) (x : F) :
    double curve (.affine x 0) = .infinity := double_y_zero curve x

example (curve : Curve F) (x y : F) (hsum : y + y ≠ 0) :
    add curve (.affine x y) (.affine x y) =
      double curve (.affine x y) :=
  add_self_of_sum_ne_zero curve x y hsum

example (curve : Curve F) (x₁ y₁ x₂ y₂ : F) (hx : x₁ ≠ x₂) :
    add curve (.affine x₁ y₁) (.affine x₂ y₂) =
      let slope := (y₂ - y₁) / (x₂ - x₁)
      let x₃ := slope ^ 2 - x₁ - x₂
      let y₃ := slope * (x₁ - x₃) - y₁
      .affine x₃ y₃ :=
  add_of_x_ne curve x₁ y₁ x₂ y₂ hx

example (curve : Curve F) (point : Point F) (h2 : (2 : F) ≠ 0) :
    OnCurve curve point -> OnCurve curve (double curve point) :=
  onCurve_double curve point h2

example (curve : Curve F) (left right : Point F) (h2 : (2 : F) ≠ 0) :
    OnCurve curve left -> OnCurve curve right ->
      OnCurve curve (add curve left right) :=
  onCurve_add curve left right h2

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulAffine.onCurve_neg' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms onCurve_neg

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulAffine.onCurve_double' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms onCurve_double

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulAffine.onCurve_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms onCurve_add

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulAffine.add_self_of_sum_ne_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms add_self_of_sum_ne_zero

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulAffine.add_of_x_ne' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms add_of_x_ne

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulAffine.infinity_add' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms infinity_add

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulAffine.add_infinity' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms add_infinity

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulAffine.double_infinity' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms double_infinity

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulAffine.double_y_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms double_y_zero

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulAffine.neg_infinity' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms neg_infinity

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulAffine.neg_affine' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms neg_affine

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulAffine.add_opposite' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms add_opposite

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulAffine.onCurve_infinity' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms onCurve_infinity

end Checks.Bls12381LawfulAffine
