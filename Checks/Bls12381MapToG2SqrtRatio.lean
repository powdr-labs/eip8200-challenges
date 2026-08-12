import Challenge.Bls12381.ProofSupport.MapToG2SqrtRatio

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.MapToG2

example : ¬ IsSquare isoZ := isoZ_not_isSquare

example (u v : Field) (hv : v ≠ 0) :
    SqrtRatioValid u v (sqrtRatioSource u v) :=
  sqrtRatioSource_valid u v hv

example (u v : Field) : sqrtRatioSource u v =
    let quotient := u * v⁻¹
    let first := Fp2.SqrtProgram.run Fp2.lawfulSqrtOps quotient
    if first.exists_ then (true, first.root)
    else
      let second := Fp2.SqrtProgram.run Fp2.lawfulSqrtOps (isoZ * quotient)
      (false, second.root) := rfl

example (u : Field) :
    ProjectiveOnCurve (sswuProjective sqrtRatioSource u) :=
  sswuSource_onCurve u

example (u : Field) : ProjectiveOnCurve (sourceSswu u) :=
  sourceSswu_onCurve u

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.isoZ_not_isSquare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isoZ_not_isSquare

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.isSquareRatio_iff_isSquare_div' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms isSquareRatio_iff_isSquare_div

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.sqrtRatioSource_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sqrtRatioSource_valid

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.sswuSource_onCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sswuSource_onCurve

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.sourceSswu_onCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sourceSswu_onCurve

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.sourceSswu_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sourceSswu_eq

end Challenge.Bls12381.ProofSupport.MapToG2
