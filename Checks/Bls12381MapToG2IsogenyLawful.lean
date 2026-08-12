import Challenge.Bls12381.ProofSupport.MapToG2IsogenyLawful

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.MapToG2

example (numerator denominator y : Field)
    (hcurve : y ^ 2 * denominator ^ 3 =
      numerator ^ 3 + isoA * numerator * denominator ^ 2 +
        isoB * denominator ^ 3) :
    G2Affine.OnCurve (iso3 numerator denominator y) :=
  iso3_onCurve numerator denominator y hcurve

/-- info: 'Challenge.Bls12381.ProofSupport.MapPolynomial.evalHom_eq_scaled_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MapPolynomial.evalHom_eq_scaled_eval

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.iso3_onCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms iso3_onCurve

end Challenge.Bls12381.ProofSupport.MapToG2
