import Challenge.Bls12381.ProofSupport.MapToG2

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.MapToG2

example : isoA = (⟨0, 240⟩ : Field) := rfl
example : isoB = (⟨1012, 1012⟩ : Field) := rfl
example : isoZ = (⟨-2, -1⟩ : Field) := rfl
example : hEff =
    0xbc69f08f2ee75b3584c6a0ea91b352888e2a8e9145ad7689986ff031508ffe1329c2f178731db956d82bf015d1212b02ec0ec69d7477c1ae954cbc06689f6a359894c0adebbf6b4e8020005aaa95551 :=
  rfl

example (u : Field) :
    let tv1 := isoZ * u ^ 2
    let tv2 := tv1 ^ 2 + tv1
    let xD := isoA * if tv2 = 0 then isoZ else -tv2
    xD ^ 2 * xD ≠ 0 :=
  sswuDenominator_ne_zero u

example (sqrtRatio : Field → Field → Bool × Field)
    (hsqrt : ∀ u v, v ≠ 0 →
      SqrtRatioValid u v (sqrtRatio u v)) (u : Field) :
    ProjectiveOnCurve (sswuProjective sqrtRatio u) :=
  sswuProjective_onCurve sqrtRatio hsqrt u

example (sqrtRatio : Field → Field → Bool × Field) (u : Field) :
    (sswuProjective sqrtRatio u).y =
      sourceSignAdjusted u (sswuSourceY0 sqrtRatio u) :=
  sswuProjective_y_eq_source sqrtRatio u

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.isoA_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isoA_ne_zero

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.isoZ_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isoZ_ne_zero

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.sswuDenominator_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sswuDenominator_ne_zero

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.sswuProjective_onCurve_of_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sswuProjective_onCurve_of_valid

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.sswuProjective_onCurve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sswuProjective_onCurve

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.sswuProjective_y_eq_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sswuProjective_y_eq_source

end Challenge.Bls12381.ProofSupport.MapToG2
