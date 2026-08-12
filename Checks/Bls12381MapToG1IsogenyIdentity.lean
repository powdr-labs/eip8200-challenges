import Challenge.Bls12381.ProofSupport.MapToG1IsogenyIdentity

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport

example {R : Type} [CommSemiring R] (left right : List R) (x : R) :
    MapPolynomial.eval (MapPolynomial.mul left right) x =
      MapPolynomial.eval left x * MapPolynomial.eval right x :=
  MapPolynomial.eval_mul left right x

example {R : Type} [CommSemiring R] (coefficients : List R)
    (exponent : Nat) (x : R) :
    MapPolynomial.eval (MapPolynomial.pow coefficients exponent) x =
      MapPolynomial.eval coefficients x ^ exponent :=
  MapPolynomial.eval_pow coefficients exponent x

/-- info: 'Challenge.Bls12381.ProofSupport.MapPolynomial.eval_mul' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MapPolynomial.eval_mul

/-- info: 'Challenge.Bls12381.ProofSupport.MapPolynomial.eval_pow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MapPolynomial.eval_pow

namespace MapToG1

example : iso11IdentityLeft = iso11IdentityRight :=
  iso11_coefficients_identity

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.iso11_coefficients_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms iso11_coefficients_identity

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG1.iso11_affine_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms iso11_affine_identity

end MapToG1
end Challenge.Bls12381.ProofSupport
