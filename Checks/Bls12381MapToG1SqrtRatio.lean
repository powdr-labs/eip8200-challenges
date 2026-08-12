import Challenge.Bls12381.ProofSupport.MapToG1Sswu

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.MapToG1

example : sqrtRatioExponent =
    (EvmSemantics.Crypto.Bls12381.p - 3) / 4 := rfl

example (u v : Field) (hv : v ≠ 0) :
    SqrtRatioValid u v (sqrtRatioSource u v) :=
  sqrtRatioSource_valid u v hv

example (u : Field) :
    ProjectiveOnCurve (sswuProjective sqrtRatioSource u) :=
  sswuSource_onCurve u

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.sqrtRatioSource_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sqrtRatioSource_valid

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.sswuSource_onCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sswuSource_onCurve

end Challenge.Bls12381.ProofSupport.MapToG1
