import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveHighMemory

set_option warningAsError true

/-! # Scheduled high left input for frozen G2ADD Fp2 products -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fp2MulLeftInput_eq_fp2At_of_high (yst : EvmState) (a b : U256)
    (haEnd : a.toNat + 96 < 2 ^ 256) (haHigh : 1632 ≤ a.toNat) :
    fp2MulLeftInput yst a b = fp2At yst a := by
  unfold fp2MulLeftInput fp2MulV0Left fp2MulV1Left fp2At
    Challenge.Bls12381.ProofSupport.Fp2.mkRepr
  dsimp only
  rw [fp2MulAfterV0Stores_loadWord_high_input yst a b
      (a + BitVec.ofNat 256 64).toNat (by bv_omega),
    fp2MulAfterV0Stores_loadWord_high_input yst a b
      (a + BitVec.ofNat 256 96).toNat (by bv_omega)]
  rfl

theorem fp2MulScheduledLeft_eq_of_high_before_out (yst : EvmState)
    (out a b : U256)
    (haEnd : a.toNat + 96 < 2 ^ 256) (haHigh : 1664 ≤ a.toNat)
    (haBefore : a.toNat + 128 ≤ out.toNat)
    (hout : out.toNat + 32 < 2 ^ 256) :
    fp2At (fp2MulAfterRealStores yst out a b) a =
      fp2MulLeftInput yst a b := by
  rw [fp2MulLeftInput_eq_fp2At_of_high yst a b haEnd (by omega)]
  apply fp2At_eq_of_loads
  all_goals
    exact fp2MulAfterRealStores_loadWord_before_out yst out a b _
      (by bv_omega) (by bv_omega) hout

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
