import Challenge.Bls12381.ProofSupport.LawfulFp2
import Challenge.Bls12381.ProofSupport.SswuCoreLawful

set_option warningAsError true

/-!
# MAP_FP2_TO_G2 shared arithmetic support

This module pins the source/RFC simplified-SWU constants and gives a
transparent projective SSWU program over the existing lawful quadratic
field. The square-root-ratio operation remains an explicit dependency with a
non-vacuous contract; its source implementation is refined separately.
-/

namespace Challenge.Bls12381.ProofSupport.MapToG2

abbrev Field := LawfulFp2.Carrier

/-- `A' = 240 * i` of the RFC 9380 G2 isogenous curve. -/
def isoA : Field := ⟨0, 240⟩

/-- `B' = 1012 * (1 + i)` of the RFC 9380 G2 isogenous curve. -/
def isoB : Field := ⟨1012, 1012⟩

/-- Source suite parameter `Z = -(2 + i)`. -/
def isoZ : Field := ⟨-2, -1⟩

/-- Exact RFC effective G2 cofactor. -/
def hEff : Nat :=
  0xbc69f08f2ee75b3584c6a0ea91b352888e2a8e9145ad7689986ff031508ffe1329c2f178731db956d82bf015d1212b02ec0ec69d7477c1ae954cbc06689f6a359894c0adebbf6b4e8020005aaa95551

theorem isoA_ne_zero : isoA ≠ 0 := by decide

theorem isoZ_ne_zero : isoZ ≠ 0 := by decide

/-- RFC Fp2 sign: sign of c0, except zero c0 defers to c1. -/
def sourceSgn0 (a : Field) : Nat :=
  if a.re.val = 0 then a.im.val % 2 else a.re.val % 2

/-- Concrete G2 suite passed to the shared simplified-SWU program. -/
def suite : SswuCore.Suite Field :=
  { A := isoA, B := isoB, Z := isoZ, sign := sourceSgn0 }

abbrev IsSquareRatio (u v : Field) : Prop :=
  SswuCore.IsSquareRatio u v

abbrev SqrtRatioValid (u v : Field) (result : Bool × Field) : Prop :=
  SswuCore.SqrtRatioValid suite u v result

abbrev SswuResult := SswuCore.Result Field

abbrev ProjectiveOnCurve (point : SswuResult) : Prop :=
  SswuCore.ProjectiveOnCurve suite point

abbrev sourceSignAdjusted (u y : Field) : Field :=
  SswuCore.signAdjusted suite u y

/-- The source CMOV makes the denominator cube passed to Fp2 sqrtRatio
nonzero for every input. -/
theorem sswuDenominator_ne_zero (u : Field) :
    let tv1 := isoZ * u ^ 2
    let tv2 := tv1 ^ 2 + tv1
    let xD := isoA * if tv2 = 0 then isoZ else -tv2
    xD ^ 2 * xD ≠ 0 := by
  simpa [SswuCore.denominator, suite] using
    SswuCore.denominator_ne_zero suite isoA_ne_zero isoZ_ne_zero u

/-- Exact decoded-field schedule of `MapFpToG2._sswuProjective`. -/
def sswuProjective
    (sqrtRatio : Field → Field → Bool × Field) (u : Field) : SswuResult :=
  SswuCore.projective suite sqrtRatio u

/-- Unsigned y candidate immediately before the source sign CMOV. -/
def sswuSourceY0
    (sqrtRatio : Field → Field → Bool × Field) (u : Field) : Field :=
  SswuCore.sourceY0 suite sqrtRatio u

theorem sswuProjective_y_eq_source
    (sqrtRatio : Field → Field → Bool × Field) (u : Field) :
    (sswuProjective sqrtRatio u).y =
      sourceSignAdjusted u (sswuSourceY0 sqrtRatio u) := by
  exact SswuCore.projective_y_eq_source suite sqrtRatio u

/-- Fixed root of the exceptional-input SSWU ratio. -/
def exceptionalRoot : Field :=
  ⟨3611395798403580372189180981549434777847917790633063236702417299179272465463714843962369288472002469087378085294992,
   423613093348586218576377851437437729690830432842722856441196780662664494552025968214749014884639894158037286276385⟩

private theorem exceptional_ratio_isSquare :
    SswuCore.ExceptionalRatioIsSquare suite := by
  unfold SswuCore.ExceptionalRatioIsSquare
  dsimp [suite]
  refine ⟨exceptionalRoot, ?_⟩
  decide

/-- Numerator passed by the source SSWU schedule to Fp2 sqrtRatio. -/
def sswuNumerator (u : Field) : Field :=
  SswuCore.numerator suite u

/-- Nonzero denominator passed by the source SSWU schedule to Fp2 sqrtRatio. -/
def sswuDenominator (u : Field) : Field :=
  SswuCore.denominator suite u

theorem sswuProjective_onCurve_of_valid
    (sqrtRatio : Field → Field → Bool × Field)
    (u : Field)
    (hvalidAt : SqrtRatioValid (sswuNumerator u) (sswuDenominator u)
      (sqrtRatio (sswuNumerator u) (sswuDenominator u))) :
    ProjectiveOnCurve (sswuProjective sqrtRatio u) := by
  exact SswuCore.projective_onCurve_of_valid suite
    exceptional_ratio_isSquare sqrtRatio u hvalidAt

theorem sswuProjective_onCurve
    (sqrtRatio : Field → Field → Bool × Field)
    (hsqrt : ∀ u v, v ≠ 0 → SqrtRatioValid u v (sqrtRatio u v))
    (u : Field) :
    ProjectiveOnCurve (sswuProjective sqrtRatio u) := by
  exact SswuCore.projective_onCurve suite isoA_ne_zero isoZ_ne_zero
    exceptional_ratio_isSquare sqrtRatio hsqrt u

end Challenge.Bls12381.ProofSupport.MapToG2
