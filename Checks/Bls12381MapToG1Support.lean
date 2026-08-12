import Challenge.Bls12381.ProofSupport.MapToG1

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.MapToG1

example : (isoA.val : Nat) =
    0x144698A3B8E9433D693A02C96D4982B0EA985383EE66A8D8E8981AEFD881AC98936F8DA0E0F97F5CF428082D584C1D :=
  isoA_val

example : (isoB.val : Nat) =
    0x12E2908D11688030018B12E8753EEE3B2016C1F0F24F4070A0B9C14FCEF35EF55A23215A316CEAA5D1CC48E98E172BE0 :=
  isoB_val

example : isoZ = 11 := rfl

example : sqrtMinusZ ^ 2 = -isoZ := sqrtMinusZ_square

example : hEff = 0xd201000000010001 := rfl

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

example :
    (sswuProjective (fun _ _ => (true, 1)) 0).y = (-1 : Field) := by
  decide

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.isoA_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isoA_val

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.isoB_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isoB_val

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.sqrtMinusZ_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sqrtMinusZ_square

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.isoA_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isoA_ne_zero

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.isoZ_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isoZ_ne_zero

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.sswuDenominator_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sswuDenominator_ne_zero

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.sswuProjective_onCurve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sswuProjective_onCurve

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.sswuProjective_onCurve_of_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sswuProjective_onCurve_of_valid

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.sswuProjective_y_eq_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sswuProjective_y_eq_source

end Challenge.Bls12381.ProofSupport.MapToG1
