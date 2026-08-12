import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveLowMemory

set_option warningAsError true

/-! # Scheduled low-memory inputs for frozen G2ADD Fp2 products -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fp2MulLeftInput_eq_fp2At_of_low (yst : EvmState) (a b : U256)
    (ha : a.toNat + 96 < 2 ^ 256) (haLow : a.toNat + 128 ≤ 1024) :
    fp2MulLeftInput yst a b = fp2At yst a := by
  have h64 : (a + BitVec.ofNat 256 64).toNat = a.toNat + 64 := by
    bv_omega
  have h96 : (a + BitVec.ofNat 256 96).toNat = a.toNat + 96 := by
    bv_omega
  unfold fp2MulLeftInput fp2MulV0Left fp2MulV1Left fp2At
    Challenge.Bls12381.ProofSupport.Fp2.mkRepr
  dsimp only
  rw [fp2MulAfterV0Stores_loadWord_before_scratch yst a b
      (a + BitVec.ofNat 256 64).toNat (by omega),
    fp2MulAfterV0Stores_loadWord_before_scratch yst a b
      (a + BitVec.ofNat 256 96).toNat (by omega)]
  rfl

theorem fp2MulRightInput_eq_fp2At_of_low (yst : EvmState) (a b : U256)
    (hb : b.toNat + 96 < 2 ^ 256) (hbLow : b.toNat + 128 ≤ 1024) :
    fp2MulRightInput yst a b = fp2At yst b := by
  have h64 : (b + BitVec.ofNat 256 64).toNat = b.toNat + 64 := by
    bv_omega
  have h96 : (b + BitVec.ofNat 256 96).toNat = b.toNat + 96 := by
    bv_omega
  unfold fp2MulRightInput fp2MulV0Right fp2MulV1Right fp2At
    Challenge.Bls12381.ProofSupport.Fp2.mkRepr
  dsimp only
  rw [fp2MulAfterV0Stores_loadWord_before_scratch yst a b
      (b + BitVec.ofNat 256 64).toNat (by omega),
    fp2MulAfterV0Stores_loadWord_before_scratch yst a b
      (b + BitVec.ofNat 256 96).toNat (by omega)]
  rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
