import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulHighInputs
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulLawful

set_option warningAsError true

/-! # Lawful high-operands-above-output endpoint for frozen G2ADD `fp2Mul` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem fp2MulFinalState_canonical_of_high_after_out
    (yst : EvmState) (out a b : U256)
    (ha : Fp2.Canonical (fp2At yst a))
    (hb : Fp2.Canonical (fp2At yst b))
    (haEnd : a.toNat + 96 < 2 ^ 256) (haHigh : 1664 ≤ a.toNat)
    (haAfter : out.toNat + 64 ≤ a.toNat)
    (hbEnd : b.toNat + 96 < 2 ^ 256) (hbHigh : 1728 ≤ b.toNat)
    (hbAfter : out.toNat + 64 ≤ b.toNat)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    Fp2.Canonical (fp2At (fp2MulFinalState yst out a b) out) := by
  have hleftInput := fp2MulLeftInput_eq_fp2At_of_high yst a b haEnd
    (by omega)
  have hrightInput := fp2MulRightInput_eq_fp2At_of_high yst a b hbEnd
    (by omega)
  apply fp2MulFinalState_canonical yst out a b
  · exact hleftInput.symm ▸ ha
  · exact hrightInput.symm ▸ hb
  · exact fp2MulScheduledLeft_eq_of_high_after_out yst out a b
      haEnd haHigh haAfter (by omega)
  · exact fp2MulScheduledRight_eq_of_high_after_out yst out a b
      hbEnd hbHigh hbAfter (by omega)
  · exact houtHigh
  · exact hout

theorem fp2MulFinalState_toLawful_mul_of_high_after_out
    (yst : EvmState) (out a b : U256)
    (ha : Fp2.Canonical (fp2At yst a))
    (hb : Fp2.Canonical (fp2At yst b))
    (haEnd : a.toNat + 96 < 2 ^ 256) (haHigh : 1664 ≤ a.toNat)
    (haAfter : out.toNat + 64 ≤ a.toNat)
    (hbEnd : b.toNat + 96 < 2 ^ 256) (hbHigh : 1728 ≤ b.toNat)
    (hbAfter : out.toNat + 64 ≤ b.toNat)
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
    (fp2MulScheduledLeft_eq_of_high_after_out yst out a b
      haEnd haHigh haAfter (by omega))
    (fp2MulScheduledRight_eq_of_high_after_out yst out a b
      hbEnd hbHigh hbAfter (by omega)) houtHigh hout

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
