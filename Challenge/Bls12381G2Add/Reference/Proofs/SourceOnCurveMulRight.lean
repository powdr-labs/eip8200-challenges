import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveMulLeft

set_option warningAsError true

/-! # Scheduled right input for frozen G2ADD Fp2 products -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fp2MulScheduledRight_eq_of_low (yst : EvmState)
    (out a b : U256)
    (hb : b.toNat + 96 < 2 ^ 256) (hbLow : b.toNat + 128 ≤ 1024)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 32 < 2 ^ 256) :
    fp2At (fp2MulAfterSumAStores yst out a b) b =
      fp2MulRightInput yst a b := by
  rw [fp2MulRightInput_eq_fp2At_of_low yst a b hb hbLow]
  apply fp2At_eq_of_loads
  all_goals
    exact fp2MulAfterSumAStores_loadWord_before_scratch yst out a b _
      (by bv_omega) houtHigh hout

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
