import Challenge.Bls12381.ProofSupport.G1Affine
import Challenge.Bls12381.ProofSupport.MapPolynomial
import Challenge.Bls12381.ProofSupport.MapToG1
import EvmSemantics.Crypto.Bls12381.MapFpToG1

set_option warningAsError true

/-!
# G1 11-isogeny support

The pinned coefficient tables are transported through the inverse-free
`Fin p ≃+* ZMod p` bridge.  Their public order is constant-first, matching the
RFC polynomial notation.  The `*SourceOrder` views reverse that order; monic
denominators additionally omit their leading coefficient exactly as the
Solidity source does.

The lawful affine endpoint treats either rational-function denominator as a
projective pole and returns infinity explicitly.  This is the mathematical
meaning of the source homogeneous result with `jZ = 0`; it avoids relying on
the pinned affine map's opaque inverse-at-zero behavior.
-/

namespace Challenge.Bls12381.ProofSupport.MapToG1

private def liftPinned
    (value : EvmSemantics.Crypto.Bls12381.Fp) : Field :=
  PrimeField.finEquiv value

/-- RFC 9380 G1 11-isogeny x-numerator coefficients, constant-first. -/
def kXNum : List Field :=
  EvmSemantics.Crypto.Bls12381MapFpToG1.kXNum.map liftPinned

/-- RFC 9380 G1 11-isogeny monic x-denominator, constant-first. -/
def kXDen : List Field :=
  EvmSemantics.Crypto.Bls12381MapFpToG1.kXDen.map liftPinned

/-- RFC 9380 G1 11-isogeny y-numerator coefficients, constant-first. -/
def kYNum : List Field :=
  EvmSemantics.Crypto.Bls12381MapFpToG1.kYNum.map liftPinned

/-- RFC 9380 G1 11-isogeny monic y-denominator, constant-first. -/
def kYDen : List Field :=
  EvmSemantics.Crypto.Bls12381MapFpToG1.kYDen.map liftPinned

/-- High-degree-first source order for the x numerator. -/
def kXNumSourceOrder : List Field := kXNum.reverse

/-- High-degree-first source order with the monic x leading term omitted. -/
def kXDenSourceOrder : List Field := kXDen.reverse.tail

/-- High-degree-first source order for the y numerator. -/
def kYNumSourceOrder : List Field := kYNum.reverse

/-- High-degree-first source order with the monic y leading term omitted. -/
def kYDenSourceOrder : List Field := kYDen.reverse.tail

theorem kXNum_length : kXNum.length = 12 := by rfl
theorem kXDen_length : kXDen.length = 11 := by rfl
theorem kYNum_length : kYNum.length = 16 := by rfl
theorem kYDen_length : kYDen.length = 16 := by rfl

/-- Four homogeneous polynomial values used by the source 11-isogeny. -/
structure Iso11Components where
  xNum : Field
  xDen : Field
  yNum : Field
  yDen : Field

/-- Exact homogeneous polynomial-evaluation boundary of `_iso11Projective`. -/
def iso11Components (numerator denominator : Field) : Iso11Components :=
  { xNum := MapPolynomial.evalHom kXNum numerator denominator
    xDen := MapPolynomial.evalHom kXDen numerator denominator
    yNum := MapPolynomial.evalHom kYNum numerator denominator
    yDen := MapPolynomial.evalHom kYDen numerator denominator }

/-- Lawful affine interpretation of the source homogeneous 11-isogeny.
Either rational-function pole maps to infinity explicitly. -/
def iso11 (numerator denominator y : Field) : G1Affine.Point :=
  let values := iso11Components numerator denominator
  let xDenominator := values.xDen * denominator
  if xDenominator = 0 ∨ values.yDen = 0 then
    G1Affine.infinity
  else
    .affine (values.xNum / xDenominator) (y * values.yNum / values.yDen)

theorem iso11_eq_infinity_of_pole (numerator denominator y : Field)
    (hpole :
      let values := iso11Components numerator denominator
      values.xDen * denominator = 0 ∨ values.yDen = 0) :
    iso11 numerator denominator y = G1Affine.infinity := by
  unfold iso11
  simp only [hpole, if_pos]

end Challenge.Bls12381.ProofSupport.MapToG1
