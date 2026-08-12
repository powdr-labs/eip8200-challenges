import Challenge.Bls12381.ProofSupport.MapToG2Isogeny
import Challenge.Bls12381.ProofSupport.MapPolynomialLawful

set_option warningAsError true

/-! # Kernel certificate for the RFC G2 3-isogeny identity -/

namespace Challenge.Bls12381.ProofSupport.MapToG2

open Challenge.Bls12381.ProofSupport

/-- Coefficients of the G2 isogenous curve equation, constant-first. -/
def isoCurveCoefficients : List Field := [isoB, isoA, 0, 1]

/-- Left side of the cleared-denominator 3-isogeny identity. -/
def iso3IdentityLeft : List Field :=
  MapPolynomial.mul
    (MapPolynomial.mul isoCurveCoefficients (MapPolynomial.pow kYNum 2))
    (MapPolynomial.pow kXDen 3)

/-- Right side of the cleared-denominator 3-isogeny identity. -/
def iso3IdentityRight : List Field :=
  MapPolynomial.add
    (MapPolynomial.mul (MapPolynomial.pow kXNum 3)
      (MapPolynomial.pow kYDen 2))
    (MapPolynomial.scale G2Affine.curve.b
      (MapPolynomial.mul (MapPolynomial.pow kXDen 3)
        (MapPolynomial.pow kYDen 2)))

/-- Kernel-reduced equality of the RFC G2 3-isogeny coefficients. -/
theorem iso3_coefficients_identity :
    iso3IdentityLeft = iso3IdentityRight := by
  decide

/-- Evaluated form of the certified G2 3-isogeny polynomial identity. -/
theorem iso3_affine_identity (x : Field) :
    (x ^ 3 + isoA * x + isoB) * MapPolynomial.eval kYNum x ^ 2 *
        MapPolynomial.eval kXDen x ^ 3 =
      MapPolynomial.eval kXNum x ^ 3 * MapPolynomial.eval kYDen x ^ 2 +
        G2Affine.curve.b * MapPolynomial.eval kXDen x ^ 3 *
          MapPolynomial.eval kYDen x ^ 2 := by
  have h := congrArg (fun coefficients => MapPolynomial.eval coefficients x)
    iso3_coefficients_identity
  simp only [iso3IdentityLeft, iso3IdentityRight, MapPolynomial.eval_mul,
    MapPolynomial.eval_pow, MapPolynomial.eval_add, MapPolynomial.eval_scale,
    isoCurveCoefficients, MapPolynomial.eval] at h
  convert h using 1 <;> ring

end Challenge.Bls12381.ProofSupport.MapToG2
