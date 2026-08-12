import Challenge.Bls12381.ProofSupport.SswuCoreLawful

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.SswuCore

def rationalSuite : Suite ℚ :=
  { A := 2, B := 3, Z := 5, sign := fun x => if x < 0 then 1 else 0 }

example (u : ℚ) :
    numerator rationalSuite u =
      let tv1 := rationalSuite.Z * u ^ 2
      let tv2 := tv1 ^ 2 + tv1
      let tv3 := rationalSuite.B * (tv2 + 1)
      let tv4 := rationalSuite.A * if tv2 = 0 then rationalSuite.Z else -tv2
      (tv3 ^ 2 + rationalSuite.A * tv4 ^ 2) * tv3 +
        rationalSuite.B * (tv4 ^ 2 * tv4) :=
  rfl

example (u : ℚ) :
    denominator rationalSuite u =
      let tv1 := rationalSuite.Z * u ^ 2
      let tv2 := tv1 ^ 2 + tv1
      let tv4 := rationalSuite.A * if tv2 = 0 then rationalSuite.Z else -tv2
      tv4 ^ 2 * tv4 :=
  rfl

example (sqrtRatio : ℚ → ℚ → Bool × ℚ) (u : ℚ) :
    (projective rationalSuite sqrtRatio u).y =
      signAdjusted rationalSuite u (sourceY0 rationalSuite sqrtRatio u) :=
  projective_y_eq_source rationalSuite sqrtRatio u

example (u : ℚ) (hA : rationalSuite.A ≠ 0)
    (hZ : rationalSuite.Z ≠ 0) :
    denominator rationalSuite u ≠ 0 :=
  denominator_ne_zero rationalSuite hA hZ u

/-- info: 'Challenge.Bls12381.ProofSupport.SswuCore.signAdjusted_sq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms signAdjusted_sq

/-- info: 'Challenge.Bls12381.ProofSupport.SswuCore.denominator_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms denominator_ne_zero

/-- info: 'Challenge.Bls12381.ProofSupport.SswuCore.projective_y_eq_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms projective_y_eq_source

/-- info: 'Challenge.Bls12381.ProofSupport.SswuCore.projective_onCurve_of_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms projective_onCurve_of_valid

/-- info: 'Challenge.Bls12381.ProofSupport.SswuCore.projective_onCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms projective_onCurve

end Challenge.Bls12381.ProofSupport.SswuCore
