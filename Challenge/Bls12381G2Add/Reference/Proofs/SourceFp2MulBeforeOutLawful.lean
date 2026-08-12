import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulHighInputs
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulLawful

set_option warningAsError true

/-! # Lawful high-operands-below-output endpoint for frozen G2ADD `fp2Mul` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem fp2MulScheduledRight_eq_of_high_before_out (yst : EvmState)
    (out a b : U256)
    (hbEnd : b.toNat + 96 < 2 ^ 256) (hbHigh : 1728 ≤ b.toNat)
    (hbBefore : b.toNat + 128 ≤ out.toNat)
    (hout : out.toNat + 32 < 2 ^ 256) :
    fp2At (fp2MulAfterSumAStores yst out a b) b =
      fp2MulRightInput yst a b := by
  rw [fp2MulRightInput_eq_fp2At_of_high yst a b hbEnd (by omega)]
  apply fp2At_eq_of_loads
  all_goals
    rw [fp2MulAfterSumAStores_loadWord_high yst out a b _ (by bv_omega)]
    exact fp2MulAfterRealStores_loadWord_before_out yst out a b _
      (by bv_omega) (by bv_omega) hout

theorem fp2MulFinalState_canonical_of_high_before_out
    (yst : EvmState) (out a b : U256)
    (ha : Fp2.Canonical (fp2At yst a))
    (hb : Fp2.Canonical (fp2At yst b))
    (haEnd : a.toNat + 96 < 2 ^ 256) (haHigh : 1664 ≤ a.toNat)
    (haBefore : a.toNat + 128 ≤ out.toNat)
    (hbEnd : b.toNat + 96 < 2 ^ 256) (hbHigh : 1728 ≤ b.toNat)
    (hbBefore : b.toNat + 128 ≤ out.toNat)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    Fp2.Canonical (fp2At (fp2MulFinalState yst out a b) out) := by
  have hleftInput := fp2MulLeftInput_eq_fp2At_of_high yst a b haEnd
    (by omega)
  have hrightInput := fp2MulRightInput_eq_fp2At_of_high yst a b hbEnd
    (by omega)
  apply fp2MulFinalState_canonical yst out a b
  · exact hleftInput.symm ▸ ha
  · exact hrightInput.symm ▸ hb
  · exact fp2MulScheduledLeft_eq_of_high_before_out yst out a b
      haEnd haHigh haBefore (by omega)
  · exact fp2MulScheduledRight_eq_of_high_before_out yst out a b
      hbEnd hbHigh hbBefore (by omega)
  · exact houtHigh
  · exact hout

theorem fp2MulFinalState_toLawful_mul_of_high_before_out
    (yst : EvmState) (out a b : U256)
    (ha : Fp2.Canonical (fp2At yst a))
    (hb : Fp2.Canonical (fp2At yst b))
    (haEnd : a.toNat + 96 < 2 ^ 256) (haHigh : 1664 ≤ a.toNat)
    (haBefore : a.toNat + 128 ≤ out.toNat)
    (hbEnd : b.toNat + 96 < 2 ^ 256) (hbHigh : 1728 ≤ b.toNat)
    (hbBefore : b.toNat + 128 ≤ out.toNat)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    Fp2.toLawful (fp2At (fp2MulFinalState yst out a b) out) =
      Fp2.toLawful (fp2At yst a) * Fp2.toLawful (fp2At yst b) := by
  have hleftInput := fp2MulLeftInput_eq_fp2At_of_high yst a b haEnd
    (by omega)
  have hrightInput := fp2MulRightInput_eq_fp2At_of_high yst a b hbEnd
    (by omega)
  rw [← hleftInput, ← hrightInput]
  exact fp2MulFinalState_toLawful_mul yst out a b
    (hleftInput.symm ▸ ha) (hrightInput.symm ▸ hb)
    (fp2MulScheduledLeft_eq_of_high_before_out yst out a b
      haEnd haHigh haBefore (by omega))
    (fp2MulScheduledRight_eq_of_high_before_out yst out a b
      hbEnd hbHigh hbBefore (by omega)) houtHigh hout

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
