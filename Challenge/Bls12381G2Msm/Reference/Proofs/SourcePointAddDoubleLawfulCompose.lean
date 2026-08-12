import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddDoubleLawfulSlope

set_option warningAsError true

/-! Composition of the opaque lawful G2MSM doubling slope stages. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport
open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

theorem pointAddDoubleFinalState_toLawful (st : EvmState) (x y : U256)
    (hx : Fp2.Canonical (fp2At (pointAddDoubleState2 st) x))
    (hy : Fp2.Canonical (fp2At (pointAddDoubleState2 st) y))
    (hxEnd : x.toNat + 96 < 2 ^ 256)
    (hxHigh : 3072 ≤ x.toNat)
    (hyEnd : y.toNat + 96 < 2 ^ 256)
    (hyHigh : 3072 ≤ y.toNat)
    (hx1 : pointAddDoubleSquareX1 (pointAddDoubleState2 st) = x)
    (hx2 : pointAddDoubleSquareX2 (pointAddDoubleState2 st) = x)
    (hy1 : pointAddDoubleDenY1 (pointAddDoubleState5 st) = y)
    (hy2 : pointAddDoubleDenY2 (pointAddDoubleState5 st) = y)
    (hy5Eq : fp2At (pointAddDoubleState5 st) y =
      fp2At (pointAddDoubleState2 st) y)
    (hnum6 : fp2At (pointAddDoubleState6 st) 2304 =
      fp2At (pointAddDoubleState5 st) 2304)
    (hnum7 : fp2At (pointAddDoubleState7 st) 2304 =
      fp2At (pointAddDoubleState6 st) 2304) :
    Fp2.toLawful (fp2At (pointAddDoubleFinalState st) 2048) =
      (3 * Fp2.toLawful (fp2At (pointAddDoubleState2 st) x) ^ 2) /
        (2 * Fp2.toLawful (fp2At (pointAddDoubleState2 st) y)) := by
  let s2 := pointAddDoubleState2 st
  have hsq := pointAddDoubleSquareState_canonical s2 x hx hxEnd hxHigh hx1 hx2
  have hsqVal := pointAddDoubleSquareState_toLawful s2 x hx hxEnd hxHigh hx1 hx2
  have hsqVal' :
      Fp2.toLawful (fp2At (pointAddDoubleState3 st) 2176) =
        Fp2.toLawful (fp2At s2 x) ^ 2 := by
    simpa only [s2, pointAddDoubleState3] using hsqVal
  have hnum2 := pointAddDoubleNum2State_canonical
    (pointAddDoubleState3 st) hsq
  have hnum2Val := pointAddDoubleNum2State_toLawful
    (pointAddDoubleState3 st) hsq
  have hsq4 : Fp2.Canonical (fp2At (pointAddDoubleState4 st) 2176) := by
    rw [show pointAddDoubleState4 st =
        pointAddDoubleNum2State (pointAddDoubleState3 st) by rfl,
      pointAddDoubleNum2State_square]
    exact hsq
  have hnum3 := pointAddDoubleNum3State_canonical
    (pointAddDoubleState4 st) hsq4 hnum2
  have hnum3Step := pointAddDoubleNum3State_toLawful
    (pointAddDoubleState4 st) hsq4 hnum2
  have hnum3Val :
      Fp2.toLawful (fp2At (pointAddDoubleState5 st) 2304) =
        3 * Fp2.toLawful (fp2At s2 x) ^ 2 := by
    rw [show pointAddDoubleState5 st =
        pointAddDoubleNum3State (pointAddDoubleState4 st) by rfl,
      hnum3Step,
      show pointAddDoubleState4 st =
        pointAddDoubleNum2State (pointAddDoubleState3 st) by rfl,
      pointAddDoubleNum2State_square,
      hnum2Val, hsqVal']
    ring
  have hy5 : Fp2.Canonical (fp2At (pointAddDoubleState5 st) y) := by
    rw [hy5Eq]
    exact hy
  have hden := pointAddDoubleDenState_canonical
    (pointAddDoubleState5 st) y hy5 hyEnd hyHigh hy1 hy2
  have hdenVal := pointAddDoubleDenState_toLawful
    (pointAddDoubleState5 st) y hy5 hyEnd hyHigh hy1 hy2
  have hy5Val : Fp2.toLawful (fp2At (pointAddDoubleState5 st) y) =
      Fp2.toLawful (fp2At (pointAddDoubleState2 st) y) := by
    rw [hy5Eq]
  have hdenVal' :
      Fp2.toLawful (fp2At (pointAddDoubleState6 st) 2432) =
        2 * Fp2.toLawful (fp2At (pointAddDoubleState2 st) y) := by
    simpa only [pointAddDoubleState6, hy5Val] using hdenVal
  have hnum6Canonical : Fp2.Canonical
      (fp2At (pointAddDoubleState6 st) 2304) := by
    rw [hnum6]
    exact hnum3
  have hinv := pointAddDoubleInvState_canonical
    (pointAddDoubleState6 st) hden
  have hinvVal := pointAddDoubleInvState_toLawful
    (pointAddDoubleState6 st) hden
  have hinvVal' :
      Fp2.toLawful (fp2At (pointAddDoubleState7 st) 2560) =
        (Fp2.toLawful (fp2At (pointAddDoubleState6 st) 2432))⁻¹ := by
    simpa only [pointAddDoubleState7] using hinvVal
  have hnum7Canonical : Fp2.Canonical
      (fp2At (pointAddDoubleState7 st) 2304) := by
    rw [hnum7]
    exact hnum6Canonical
  rw [show pointAddDoubleFinalState st =
      pointAddDoubleSlopeState (pointAddDoubleState7 st) by rfl,
    pointAddDoubleSlopeState_toLawful _ hnum7Canonical hinv,
    hnum7, hnum6, hnum3Val,
    hinvVal', hdenVal']
  rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
