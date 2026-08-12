import Challenge.Bls12381.ProofSupport.G2Affine
import Challenge.Bls12381.ProofSupport.MapPolynomial
import Challenge.Bls12381.ProofSupport.MapToG2
import EvmSemantics.Crypto.Bls12381.MapFp2ToG2

set_option warningAsError true

/-!
# G2 3-isogeny support

The pinned RFC coefficient tables are transported through the inverse-free
Fp2 wire bridge.  Public coefficient lists are constant-first.  The source
views are high-degree-first and omit the leading coefficient of monic
denominators.

The pinned x-denominator table contains a harmless trailing zero used to pad
all four tables to the same length.  `kXDen` removes that padding so its
homogeneous degree is exactly two, matching `_evalPolyMonicHom` in Solidity.

Either rational-function denominator zero is interpreted as the projective
identity.  This is the affine meaning of the source homogeneous Jacobian
output with `jZ = 0`.
-/

namespace Challenge.Bls12381.ProofSupport.MapToG2

private def liftPinned
    (value : EvmSemantics.Crypto.Bls12381.Fp2) : Field :=
  LawfulFp2.ofWire value

/-- RFC G2 3-isogeny x-numerator coefficients, constant-first. -/
def kXNum : List Field :=
  EvmSemantics.Crypto.Bls12381MapFp2ToG2.kXNum.map liftPinned

/-- RFC G2 3-isogeny monic degree-two x-denominator, constant-first.
The pinned fourth zero padding coefficient is deliberately removed. -/
def kXDen : List Field :=
  (EvmSemantics.Crypto.Bls12381MapFp2ToG2.kXDen.map liftPinned).take 3

/-- RFC G2 3-isogeny y-numerator coefficients, constant-first. -/
def kYNum : List Field :=
  EvmSemantics.Crypto.Bls12381MapFp2ToG2.kYNum.map liftPinned

/-- RFC G2 3-isogeny monic y-denominator, constant-first. -/
def kYDen : List Field :=
  EvmSemantics.Crypto.Bls12381MapFp2ToG2.kYDen.map liftPinned

/-- High-degree-first source order for the x numerator. -/
def kXNumSourceOrder : List Field := kXNum.reverse

/-- High-degree-first source order with the monic x leading term omitted. -/
def kXDenSourceOrder : List Field := kXDen.reverse.tail

/-- High-degree-first source order for the y numerator. -/
def kYNumSourceOrder : List Field := kYNum.reverse

/-- High-degree-first source order with the monic y leading term omitted. -/
def kYDenSourceOrder : List Field := kYDen.reverse.tail

theorem kXNum_length : kXNum.length = 4 := by rfl
theorem kXDen_length : kXDen.length = 3 := by rfl
theorem kYNum_length : kYNum.length = 4 := by rfl
theorem kYDen_length : kYDen.length = 4 := by rfl

/-- The extra pinned x-denominator entry is exactly zero padding. -/
theorem kXDen_pinned_padding :
    EvmSemantics.Crypto.Bls12381MapFp2ToG2.kXDen.map liftPinned =
      kXDen ++ [0] := by rfl

theorem kXDenSourceOrder_length : kXDenSourceOrder.length = 2 := by rfl
theorem kYDenSourceOrder_length : kYDenSourceOrder.length = 3 := by rfl

/-- Four homogeneous polynomial values used by the source 3-isogeny. -/
structure Iso3Components where
  xNum : Field
  xDen : Field
  yNum : Field
  yDen : Field

/-- Exact homogeneous polynomial-evaluation boundary of `_iso3Projective`. -/
def iso3Components (numerator denominator : Field) : Iso3Components :=
  { xNum := MapPolynomial.evalHom kXNum numerator denominator
    xDen := MapPolynomial.evalHom kXDen numerator denominator
    yNum := MapPolynomial.evalHom kYNum numerator denominator
    yDen := MapPolynomial.evalHom kYDen numerator denominator }

/-- Lawful affine interpretation of the source homogeneous 3-isogeny.
Either rational-function pole maps to infinity explicitly. -/
def iso3 (numerator denominator y : Field) : G2Affine.Point :=
  let values := iso3Components numerator denominator
  let xDenominator := values.xDen * denominator
  if xDenominator = 0 ∨ values.yDen = 0 then
    G2Affine.infinity
  else
    .affine (values.xNum / xDenominator) (y * values.yNum / values.yDen)

theorem iso3_eq_infinity_of_pole (numerator denominator y : Field)
    (hpole :
      let values := iso3Components numerator denominator
      values.xDen * denominator = 0 ∨ values.yDen = 0) :
    iso3 numerator denominator y = G2Affine.infinity := by
  unfold iso3
  simp only [hpole, if_pos]

end Challenge.Bls12381.ProofSupport.MapToG2
