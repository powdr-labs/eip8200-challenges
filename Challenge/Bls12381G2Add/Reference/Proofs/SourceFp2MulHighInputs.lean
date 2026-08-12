import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveHighInputs
import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveMulRight

set_option warningAsError true

/-! # High operands above the output for frozen G2ADD `fp2Mul` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fp2MulRightInput_eq_fp2At_of_high (yst : EvmState) (a b : U256)
    (hbEnd : b.toNat + 96 < 2 ^ 256) (hbHigh : 1632 ≤ b.toNat) :
    fp2MulRightInput yst a b = fp2At yst b := by
  unfold fp2MulRightInput fp2MulV0Right fp2MulV1Right fp2At
    Challenge.Bls12381.ProofSupport.Fp2.mkRepr
  dsimp only
  rw [fp2MulAfterV0Stores_loadWord_high_input yst a b
      (b + BitVec.ofNat 256 64).toNat (by bv_omega),
    fp2MulAfterV0Stores_loadWord_high_input yst a b
      (b + BitVec.ofNat 256 96).toNat (by bv_omega)]
  rfl

private theorem fp2MulAfterRealStores_loadWord_after_out_high
    (yst : EvmState) (out a b : U256) (offset : Nat)
    (hstart : 1664 ≤ offset) (hafter : out.toNat + 64 ≤ offset)
    (hout : out.toNat + 32 < 2 ^ 256) :
    loadWord (fp2MulAfterRealStores yst out a b).memory offset =
      loadWord yst.memory offset := by
  have h32 : (out + BitVec.ofNat 256 32).toNat = out.toNat + 32 := by
    bv_omega
  rw [fp2MulAfterRealStores, fp2MulAfterRealHigh]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterRealReads yst a b).memory out.toNat _)
      (out + BitVec.ofNat 256 32).toNat _) offset = _
  rw [h32,
    loadWord_storeWord_disjoint _ (out.toNat + 32) offset _
      (by left; omega),
    loadWord_storeWord_disjoint _ out.toNat offset _ (by left; omega)]
  exact fp2MulAfterV1Stores_loadWord_high_input yst a b offset hstart

theorem fp2MulScheduledLeft_eq_of_high_after_out (yst : EvmState)
    (out a b : U256)
    (haEnd : a.toNat + 96 < 2 ^ 256) (haHigh : 1664 ≤ a.toNat)
    (haAfter : out.toNat + 64 ≤ a.toNat)
    (hout : out.toNat + 32 < 2 ^ 256) :
    fp2At (fp2MulAfterRealStores yst out a b) a =
      fp2MulLeftInput yst a b := by
  rw [fp2MulLeftInput_eq_fp2At_of_high yst a b haEnd (by omega)]
  apply fp2At_eq_of_loads
  all_goals
    exact fp2MulAfterRealStores_loadWord_after_out_high yst out a b _
      (by bv_omega) (by bv_omega) hout

theorem fp2MulScheduledRight_eq_of_high_after_out (yst : EvmState)
    (out a b : U256)
    (hbEnd : b.toNat + 96 < 2 ^ 256) (hbHigh : 1728 ≤ b.toNat)
    (hbAfter : out.toNat + 64 ≤ b.toNat)
    (hout : out.toNat + 32 < 2 ^ 256) :
    fp2At (fp2MulAfterSumAStores yst out a b) b =
      fp2MulRightInput yst a b := by
  rw [fp2MulRightInput_eq_fp2At_of_high yst a b hbEnd (by omega)]
  apply fp2At_eq_of_loads
  all_goals
    rw [fp2MulAfterSumAStores_loadWord_high yst out a b _ (by bv_omega)]
    exact fp2MulAfterRealStores_loadWord_after_out_high yst out a b _
      (by bv_omega) (by bv_omega) hout

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
