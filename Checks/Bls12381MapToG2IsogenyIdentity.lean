import Challenge.Bls12381.ProofSupport.MapToG2IsogenyIdentity

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.MapToG2

open Challenge.Bls12381.ProofSupport

example (x : Field) :
    (x ^ 3 + isoA * x + isoB) * MapPolynomial.eval kYNum x ^ 2 *
        MapPolynomial.eval kXDen x ^ 3 =
      MapPolynomial.eval kXNum x ^ 3 * MapPolynomial.eval kYDen x ^ 2 +
        G2Affine.curve.b * MapPolynomial.eval kXDen x ^ 3 *
          MapPolynomial.eval kYDen x ^ 2 :=
  iso3_affine_identity x

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.iso3_coefficients_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms iso3_coefficients_identity

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.iso3_affine_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms iso3_affine_identity

end Challenge.Bls12381.ProofSupport.MapToG2
