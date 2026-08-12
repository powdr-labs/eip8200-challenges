import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2AddAfterLawful
import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddDoubleBranch

set_option warningAsError true

/-! Lawful slope arithmetic for the fixed-layout G2MSM doubling branch. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport
open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

private theorem nat_2176 : ((2176 : U256).toNat) = 2176 := by decide

private theorem pointAddDoubleSquareRead2_fp2At (st : EvmState)
    (ptr : U256) :
    fp2At (pointAddDoubleSquareRead2 st) ptr = fp2At st ptr := by
  rfl

theorem pointAddDoubleSquareState_canonical (st : EvmState) (x : U256)
    (hx : Fp2.Canonical (fp2At st x))
    (hxEnd : x.toNat + 96 < 2 ^ 256)
    (hxHigh : 3072 ≤ x.toNat)
    (hx1 : pointAddDoubleSquareX1 st = x)
    (hx2 : pointAddDoubleSquareX2 st = x) :
    Fp2.Canonical (fp2At (pointAddDoubleSquareState st) 2176) := by
  unfold pointAddDoubleSquareState
  rw [hx1, hx2]
  apply fp2MulFinalState_canonical_after
  · rw [pointAddDoubleSquareRead2_fp2At]
    exact hx
  · rw [pointAddDoubleSquareRead2_fp2At]
    exact hx
  · exact hxEnd
  · omega
  · rw [nat_2176]
    omega
  · exact hxEnd
  · omega
  · rw [nat_2176]
    omega
  · decide
  · decide

theorem pointAddDoubleSquareState_toLawful (st : EvmState) (x : U256)
    (hx : Fp2.Canonical (fp2At st x))
    (hxEnd : x.toNat + 96 < 2 ^ 256)
    (hxHigh : 3072 ≤ x.toNat)
    (hx1 : pointAddDoubleSquareX1 st = x)
    (hx2 : pointAddDoubleSquareX2 st = x) :
    Fp2.toLawful (fp2At (pointAddDoubleSquareState st) 2176) =
      Fp2.toLawful (fp2At st x) ^ 2 := by
  unfold pointAddDoubleSquareState
  rw [hx1, hx2]
  have h := fp2MulFinalState_toLawful_after
    (pointAddDoubleSquareRead2 st) 2176 x x
    (by rw [pointAddDoubleSquareRead2_fp2At]; exact hx)
    (by rw [pointAddDoubleSquareRead2_fp2At]; exact hx)
    hxEnd (by omega) (by rw [nat_2176]; omega)
    hxEnd (by omega) (by rw [nat_2176]; omega)
    (by decide) (by decide)
  rw [pointAddDoubleSquareRead2_fp2At] at h
  simpa only [pow_two] using h

theorem pointAddDoubleNum2State_canonical (st : EvmState)
    (hsq : Fp2.Canonical (fp2At st 2176)) :
    Fp2.Canonical (fp2At (pointAddDoubleNum2State st) 2304) := by
  unfold pointAddDoubleNum2State
  exact fp2AddFinalState_canonical_before st 2304 2176 2176 hsq hsq
    (by decide) (by decide) (by decide)

theorem pointAddDoubleNum2State_toLawful (st : EvmState)
    (hsq : Fp2.Canonical (fp2At st 2176)) :
    Fp2.toLawful (fp2At (pointAddDoubleNum2State st) 2304) =
      2 * Fp2.toLawful (fp2At st 2176) := by
  unfold pointAddDoubleNum2State
  rw [fp2AddFinalState_toLawful_before st 2304 2176 2176 hsq hsq
    (by decide) (by decide) (by decide)]
  ring

theorem pointAddDoubleNum2State_square (st : EvmState) :
    fp2At (pointAddDoubleNum2State st) 2176 = fp2At st 2176 := by
  unfold pointAddDoubleNum2State
  exact fp2AddFinalState_fp2At_before_out _ _ _ _ _
    (by decide) (by decide) (by decide)

theorem pointAddDoubleNum3State_canonical (st : EvmState)
    (hsq : Fp2.Canonical (fp2At st 2176))
    (hnum2 : Fp2.Canonical (fp2At st 2304)) :
    Fp2.Canonical (fp2At (pointAddDoubleNum3State st) 2304) := by
  unfold pointAddDoubleNum3State
  apply fp2AddFinalState_canonical_at_out_before
  · exact hnum2
  · exact hsq
  · decide
  · decide

theorem pointAddDoubleNum3State_toLawful (st : EvmState)
    (hsq : Fp2.Canonical (fp2At st 2176))
    (hnum2 : Fp2.Canonical (fp2At st 2304)) :
    Fp2.toLawful (fp2At (pointAddDoubleNum3State st) 2304) =
      Fp2.toLawful (fp2At st 2304) + Fp2.toLawful (fp2At st 2176) := by
  unfold pointAddDoubleNum3State
  rw [fp2AddFinalState_toLawful_at_out_before st 2304 2176 hnum2
    hsq (by decide) (by decide)]

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
