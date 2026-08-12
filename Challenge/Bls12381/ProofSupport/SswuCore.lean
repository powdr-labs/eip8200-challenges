import Mathlib.Algebra.Field.Defs

set_option warningAsError true

/-!
# Generic simplified-SWU source schedule

This definition-only module contains the decoded-field control flow shared by
the BLS12-381 G1 and G2 mapping suites.  Concrete modules provide their own
field, curve coefficients, suite parameter, and sign function.
-/

namespace Challenge.Bls12381.ProofSupport.SswuCore

/-- Parameters of a simplified-SWU suite at the decoded-field boundary. -/
structure Suite (F : Type*) where
  A : F
  B : F
  Z : F
  sign : F → Nat

/-- A ratio is square without introducing partial division. -/
def IsSquareRatio {F : Type*} [Monoid F] (u v : F) : Prop :=
  ∃ y, y ^ 2 * v = u

/-- Source square-root-ratio contract for a suite parameter `Z`. -/
def SqrtRatioValid {F : Type*} [Monoid F] (suite : Suite F)
    (u v : F) (result : Bool × F) : Prop :=
  if result.1 then result.2 ^ 2 * v = u
  else result.2 ^ 2 * v = suite.Z * u ∧ ¬ IsSquareRatio u v

/-- Runtime result of the exact projective simplified-SWU schedule. -/
structure Result (F : Type*) where
  xN : F
  xD : F
  y : F

/-- Homogeneous membership on `y² = x³ + A*x + B`, with `x=xN/xD`. -/
def ProjectiveOnCurve {F : Type*} [CommRing F] (suite : Suite F)
    (point : Result F) : Prop :=
  point.y ^ 2 * point.xD ^ 3 =
    point.xN ^ 3 + suite.A * point.xN * point.xD ^ 2 +
      suite.B * point.xD ^ 3

/-- Exact source sign selection at the decoded-field boundary. -/
def signAdjusted {F : Type*} [Neg F] [DecidableEq Nat]
    (suite : Suite F) (u y : F) : F :=
  if suite.sign u = suite.sign y then y else -y

/-- Numerator passed by the source SSWU schedule to square-root-ratio. -/
def numerator {F : Type*} [Field F] [DecidableEq F]
    (suite : Suite F) (u : F) : F :=
  let tv1 := suite.Z * u ^ 2
  let tv2 := tv1 ^ 2 + tv1
  let tv3 := suite.B * (tv2 + 1)
  let tv4 := suite.A * if tv2 = 0 then suite.Z else -tv2
  (tv3 ^ 2 + suite.A * tv4 ^ 2) * tv3 +
    suite.B * (tv4 ^ 2 * tv4)

/-- Nonzero-by-construction denominator passed to square-root-ratio. -/
def denominator {F : Type*} [Field F] [DecidableEq F]
    (suite : Suite F) (u : F) : F :=
  let tv1 := suite.Z * u ^ 2
  let tv2 := tv1 ^ 2 + tv1
  let tv4 := suite.A * if tv2 = 0 then suite.Z else -tv2
  tv4 ^ 2 * tv4

/-- Unsigned `y` candidate immediately before the source sign CMOV. -/
def sourceY0 {F : Type*} [Field F] [DecidableEq F]
    (suite : Suite F) (sqrtRatio : F → F → Bool × F) (u : F) : F :=
  let tv1 := suite.Z * u ^ 2
  let tv2 := tv1 ^ 2 + tv1
  let tv3 := suite.B * (tv2 + 1)
  let tv4 := suite.A * if tv2 = 0 then suite.Z else -tv2
  let ratio := sqrtRatio
    ((tv3 ^ 2 + suite.A * tv4 ^ 2) * tv3 +
      suite.B * (tv4 ^ 2 * tv4))
    (tv4 ^ 2 * tv4)
  if ratio.1 then ratio.2 else tv1 * u * ratio.2

/-- Exact decoded-field source projective SSWU schedule. -/
def projective {F : Type*} [Field F] [DecidableEq F]
    (suite : Suite F) (sqrtRatio : F → F → Bool × F)
    (u : F) : Result F :=
  let tv1 := suite.Z * u ^ 2
  let tv2 := tv1 ^ 2 + tv1
  let tv3 := suite.B * (tv2 + 1)
  let tv4 := suite.A * if tv2 = 0 then suite.Z else -tv2
  let ratio := sqrtRatio
    ((tv3 ^ 2 + suite.A * tv4 ^ 2) * tv3 +
      suite.B * (tv4 ^ 2 * tv4))
    (tv4 ^ 2 * tv4)
  let xN := if ratio.1 then tv3 else tv1 * tv3
  let y0 := if ratio.1 then ratio.2 else tv1 * u * ratio.2
  { xN, xD := tv4, y := signAdjusted suite u y0 }

end Challenge.Bls12381.ProofSupport.SswuCore
