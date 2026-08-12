import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveX2

set_option warningAsError true

/-! # High intermediate locality used by frozen G2ADD `onCurve` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fp2MulAfterV0Stores_loadWord_high_input
    (yst : EvmState) (a b : U256) (offset : Nat) (hstart : 1632 ≤ offset) :
    loadWord (fp2MulAfterV0Stores yst a b).memory offset =
      loadWord yst.memory offset := by
  rw [fp2MulAfterV0Stores, fp2MulAfterV0High]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterV0Call yst a b).memory 1536
        (fp2MulV0 yst a b).1)
      1568 (fp2MulV0 yst a b).2) offset = _
  rw [loadWord_storeWord_disjoint _ 1568 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1536 offset _ (by omega)]
  unfold fp2MulAfterV0Call
  rw [fpMulFinalState_loadWord_after_scratch (hstart := by omega)]
  rfl

theorem fp2MulAfterV1Stores_loadWord_high_input
    (yst : EvmState) (a b : U256) (offset : Nat) (hstart : 1664 ≤ offset) :
    loadWord (fp2MulAfterV1Stores yst a b).memory offset =
      loadWord yst.memory offset := by
  rw [fp2MulAfterV1Stores, fp2MulAfterV1High]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterV1Call yst a b).memory 1600
        (fp2MulV1 yst a b).1)
      1632 (fp2MulV1 yst a b).2) offset = _
  rw [loadWord_storeWord_disjoint _ 1632 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1600 offset _ (by omega)]
  unfold fp2MulAfterV1Call
  rw [fpMulFinalState_loadWord_after_scratch (hstart := by omega)]
  exact fp2MulAfterV0Stores_loadWord_high_input yst a b offset (by omega)

theorem fp2MulAfterRealStores_loadWord_before_out
    (yst : EvmState) (out a b : U256) (offset : Nat)
    (hstart : 1664 ≤ offset) (hend : offset + 32 ≤ out.toNat)
    (houtEnd : out.toNat + 32 < 2 ^ 256) :
    loadWord (fp2MulAfterRealStores yst out a b).memory offset =
      loadWord yst.memory offset := by
  rw [fp2MulAfterRealStores, fp2MulAfterRealHigh]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterRealReads yst a b).memory out.toNat
        (fp2MulReal yst a b).1)
      (out + BitVec.ofNat 256 32).toNat (fp2MulReal yst a b).2) offset = _
  rw [loadWord_storeWord_disjoint _
      (out + BitVec.ofNat 256 32).toNat offset _ (by right; bv_omega),
    loadWord_storeWord_disjoint _ out.toNat offset _ (by right; omega)]
  exact fp2MulAfterV1Stores_loadWord_high_input yst a b offset hstart

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
