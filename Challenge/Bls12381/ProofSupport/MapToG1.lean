import Challenge.Bls12381.ProofSupport.FpSqrtLawful
import Challenge.Bls12381.ProofSupport.SswuCoreLawful

set_option warningAsError true

/-!
# MAP_FP_TO_G1 shared arithmetic support

This module pins the source/RFC simplified-SWU constants and gives a
transparent projective SSWU program over the existing lawful base field.  The
square-root-ratio operation is an explicit parameter with a reusable contract;
the source exponentiation routine can refine that contract independently.
-/

namespace Challenge.Bls12381.ProofSupport.MapToG1

abbrev Field := PrimeField.LawfulFp

/-- `A'` of the RFC 9380 G1 isogenous curve. -/
def isoA : Field :=
  0x144698A3B8E9433D693A02C96D4982B0EA985383EE66A8D8E8981AEFD881AC98936F8DA0E0F97F5CF428082D584C1D

/-- `B'` of the RFC 9380 G1 isogenous curve. -/
def isoB : Field :=
  0x12E2908D11688030018B12E8753EEE3B2016C1F0F24F4070A0B9C14FCEF35EF55A23215A316CEAA5D1CC48E98E172BE0

/-- Source suite parameter `Z = 11`. -/
def isoZ : Field := 11

/-- Exact source `sqrt(-Z)` constant passed to `Fp.sqrtRatio`. -/
def sqrtMinusZ : Field :=
  0x04610E003BD3AC94DFA9246C390D7A78942602029175A4CA366D601F33F3946E3ED39794735C38315D874BC1D70637C3

/-- EIP/RFC effective G1 cofactor. -/
def hEff : Nat := 0xd201000000010001

theorem isoA_val : isoA.val =
    0x144698A3B8E9433D693A02C96D4982B0EA985383EE66A8D8E8981AEFD881AC98936F8DA0E0F97F5CF428082D584C1D := by
  rw [isoA, ZMod.val_ofNat]
  norm_num [EvmSemantics.Crypto.Bls12381.p,
    EvmSemantics.Crypto.Bls12381.absU]

theorem isoB_val : isoB.val =
    0x12E2908D11688030018B12E8753EEE3B2016C1F0F24F4070A0B9C14FCEF35EF55A23215A316CEAA5D1CC48E98E172BE0 := by
  rw [isoB, ZMod.val_ofNat]
  norm_num [EvmSemantics.Crypto.Bls12381.p,
    EvmSemantics.Crypto.Bls12381.absU]

theorem sqrtMinusZ_square : sqrtMinusZ ^ 2 = -isoZ := by
  decide

theorem isoA_ne_zero : isoA ≠ 0 := by decide

theorem isoZ_ne_zero : isoZ ≠ 0 := by decide

/-- Concrete G1 suite passed to the shared simplified-SWU program. -/
def suite : SswuCore.Suite Field :=
  { A := isoA, B := isoB, Z := isoZ, sign := fun x => x.val % 2 }

abbrev IsSquareRatio (u v : Field) : Prop :=
  SswuCore.IsSquareRatio u v

abbrev SqrtRatioValid (u v : Field) (result : Bool × Field) : Prop :=
  SswuCore.SqrtRatioValid suite u v result

abbrev SswuResult := SswuCore.Result Field

abbrev ProjectiveOnCurve (point : SswuResult) : Prop :=
  SswuCore.ProjectiveOnCurve suite point

abbrev sourceSignAdjusted (u y : Field) : Field :=
  SswuCore.signAdjusted suite u y

/-- The source CMOV makes the denominator cube passed to `sqrtRatio`
nonzero for every input. -/
theorem sswuDenominator_ne_zero (u : Field) :
    let tv1 := isoZ * u ^ 2
    let tv2 := tv1 ^ 2 + tv1
    let xD := isoA * if tv2 = 0 then isoZ else -tv2
    xD ^ 2 * xD ≠ 0 := by
  simpa [SswuCore.denominator, suite] using
    SswuCore.denominator_ne_zero suite isoA_ne_zero isoZ_ne_zero u

/-- Exact decoded-field schedule of `MapFpToG1._sswuProjective`. -/
def sswuProjective
    (sqrtRatio : Field → Field → Bool × Field) (u : Field) : SswuResult :=
  SswuCore.projective suite sqrtRatio u

/-- The unsigned `y` candidate immediately before the source sign CMOV.  This
audit helper mirrors the schedule without entering the executable call graph. -/
def sswuSourceY0
    (sqrtRatio : Field → Field → Bool × Field) (u : Field) : Field :=
  SswuCore.sourceY0 suite sqrtRatio u

/-- Observable source refinement for the final sign-selection branch.  Unlike
the on-curve theorem, this equality detects omitting or reversing the CMOV. -/
theorem sswuProjective_y_eq_source
    (sqrtRatio : Field → Field → Bool × Field) (u : Field) :
    (sswuProjective sqrtRatio u).y =
      sourceSignAdjusted u (sswuSourceY0 sqrtRatio u) := by
  exact SswuCore.projective_y_eq_source suite sqrtRatio u

/-- Fixed witness that the exceptional-denominator ratio is quadratic. -/
def exceptionalRoot : Field :=
  0x05BE3446F07E910E291153E84F1DABD3DFE5C2B1080D8B6A640425C3826F2A429373F9BAB7E8308F6DD10FFA11124DBC

private theorem exceptional_ratio_isSquare :
    SswuCore.ExceptionalRatioIsSquare suite := by
  unfold SswuCore.ExceptionalRatioIsSquare
  dsimp [suite]
  refine ⟨exceptionalRoot, ?_⟩
  decide

/-- Numerator passed by the source SSWU schedule to `Fp.sqrtRatio`. -/
def sswuNumerator (u : Field) : Field :=
  SswuCore.numerator suite u

/-- Nonzero denominator passed by the source SSWU schedule to `Fp.sqrtRatio`. -/
def sswuDenominator (u : Field) : Field :=
  SswuCore.denominator suite u

/-- The exact projective SSWU schedule lands on the pinned isogenous curve
when the concrete numerator/denominator result satisfies the source contract. -/
theorem sswuProjective_onCurve_of_valid
    (sqrtRatio : Field → Field → Bool × Field)
    (u : Field)
    (hvalidAt : SqrtRatioValid (sswuNumerator u) (sswuDenominator u)
      (sqrtRatio (sswuNumerator u) (sswuDenominator u))) :
    ProjectiveOnCurve (sswuProjective sqrtRatio u) := by
  exact SswuCore.projective_onCurve_of_valid suite
    exceptional_ratio_isSquare sqrtRatio u hvalidAt

/-- The exact projective SSWU schedule lands on the pinned isogenous curve
whenever its square-root-ratio dependency satisfies the source contract. -/
theorem sswuProjective_onCurve
    (sqrtRatio : Field → Field → Bool × Field)
    (hsqrt : ∀ u v, v ≠ 0 → SqrtRatioValid u v (sqrtRatio u v))
    (u : Field) :
    ProjectiveOnCurve (sswuProjective sqrtRatio u) := by
  exact SswuCore.projective_onCurve suite isoA_ne_zero isoZ_ne_zero
    exceptional_ratio_isSquare sqrtRatio hsqrt u

end Challenge.Bls12381.ProofSupport.MapToG1
