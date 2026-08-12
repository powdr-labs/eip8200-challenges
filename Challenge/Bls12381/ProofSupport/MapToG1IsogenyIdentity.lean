import Challenge.Bls12381.ProofSupport.MapPolynomial
import Challenge.Bls12381.ProofSupport.MapPolynomialLawful
import Challenge.Bls12381.ProofSupport.MapToG1Isogeny

set_option warningAsError true

/-! # Kernel certificate for the RFC G1 11-isogeny identity -/

namespace Challenge.Bls12381.ProofSupport.MapToG1

open Challenge.Bls12381.ProofSupport

/-- Coefficients of the G1 isogenous curve equation, constant-first. -/
def isoCurveCoefficients : List Field := [isoB, isoA, 0, 1]

/-- Left side of the cleared-denominator isogeny identity. -/
def iso11IdentityLeft : List Field :=
  MapPolynomial.mul
    (MapPolynomial.mul isoCurveCoefficients (MapPolynomial.pow kYNum 2))
    (MapPolynomial.pow kXDen 3)

/-- Right side of the cleared-denominator isogeny identity. -/
def iso11IdentityRight : List Field :=
  MapPolynomial.add
    (MapPolynomial.mul (MapPolynomial.pow kXNum 3)
      (MapPolynomial.pow kYDen 2))
    (MapPolynomial.scale 4
      (MapPolynomial.mul (MapPolynomial.pow kXDen 3)
        (MapPolynomial.pow kYDen 2)))

/-- Kernel-reduced equality of all 64 coefficients in the degree-63 RFC
11-isogeny identity. -/
theorem iso11_coefficients_identity :
    iso11IdentityLeft = iso11IdentityRight := by
  decide

/-- Evaluated form of the certified 11-isogeny polynomial identity. -/
theorem iso11_affine_identity (x : Field) :
    (x ^ 3 + isoA * x + isoB) * MapPolynomial.eval kYNum x ^ 2 *
        MapPolynomial.eval kXDen x ^ 3 =
      MapPolynomial.eval kXNum x ^ 3 * MapPolynomial.eval kYDen x ^ 2 +
        4 * MapPolynomial.eval kXDen x ^ 3 *
          MapPolynomial.eval kYDen x ^ 2 := by
  have h := congrArg (fun coefficients => MapPolynomial.eval coefficients x)
    iso11_coefficients_identity
  simp only [iso11IdentityLeft, iso11IdentityRight, MapPolynomial.eval_mul,
    MapPolynomial.eval_pow, MapPolynomial.eval_add, MapPolynomial.eval_scale,
    isoCurveCoefficients, MapPolynomial.eval] at h
  convert h using 1 <;> ring

end Challenge.Bls12381.ProofSupport.MapToG1
