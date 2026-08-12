import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulLawful
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulMemory

set_option warningAsError true

/-! # Low-input locality used by frozen G2ADD `onCurve` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fpMulFinalState_loadWord_before_scratch (yst : EvmState)
    (ahi alo bhi blo : U256) (offset : Nat)
    (hend : offset + 32 ≤ 1024) :
    loadWord (fpMulFinalState yst ahi alo bhi blo).memory offset =
      loadWord yst.memory offset :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulFinalState_loadWord_before_scratch
    yst ahi alo bhi blo offset hend

theorem fp2MulAfterV0Stores_loadWord_before_scratch
    (yst : EvmState) (a b : U256) (offset : Nat)
    (hend : offset + 32 ≤ 1024) :
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
  rw [fpMulFinalState_loadWord_before_scratch _ _ _ _ _ offset hend]
  rfl

theorem fp2MulAfterV1Stores_loadWord_before_scratch
    (yst : EvmState) (a b : U256) (offset : Nat)
    (hend : offset + 32 ≤ 1024) :
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
  rw [fpMulFinalState_loadWord_before_scratch _ _ _ _ _ offset hend]
  exact fp2MulAfterV0Stores_loadWord_before_scratch yst a b offset hend

theorem fp2MulAfterRealStores_loadWord_before_scratch
    (yst : EvmState) (out a b : U256) (offset : Nat)
    (hend : offset + 32 ≤ 1024) (hout : 1920 ≤ out.toNat)
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
  exact fp2MulAfterV1Stores_loadWord_before_scratch yst a b offset hend

theorem fp2MulAfterSumAStores_loadWord_before_scratch
    (yst : EvmState) (out a b : U256) (offset : Nat)
    (hend : offset + 32 ≤ 1024) (hout : 1920 ≤ out.toNat)
    (houtEnd : out.toNat + 32 < 2 ^ 256) :
    loadWord (fp2MulAfterSumAStores yst out a b).memory offset =
      loadWord yst.memory offset := by
  rw [fp2MulAfterSumAStores, fp2MulAfterSumAHigh]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterRealStores yst out a b).memory 1664
        (fp2MulSumA yst out a b).1)
      1696 (fp2MulSumA yst out a b).2) offset = _
  rw [loadWord_storeWord_disjoint _ 1696 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1664 offset _ (by omega),
    fp2MulAfterRealStores_loadWord_before_scratch yst out a b offset hend hout
      houtEnd]

private theorem fp2MulAfterSumBStores_loadWord_before_scratch
    (yst : EvmState) (out a b : U256) (offset : Nat)
    (hend : offset + 32 ≤ 1024) (hout : 1920 ≤ out.toNat)
    (houtEnd : out.toNat + 32 < 2 ^ 256) :
    loadWord (fp2MulAfterSumBStores yst out a b).memory offset =
      loadWord yst.memory offset := by
  rw [fp2MulAfterSumBStores, fp2MulAfterSumBHigh]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterSumAStores yst out a b).memory 1728
        (fp2MulSumB yst out a b).1)
      1760 (fp2MulSumB yst out a b).2) offset = _
  rw [loadWord_storeWord_disjoint _ 1760 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1728 offset _ (by omega),
    fp2MulAfterSumAStores_loadWord_before_scratch yst out a b offset hend hout
      houtEnd]

private theorem fp2MulAfterCrossStores_loadWord_before_scratch
    (yst : EvmState) (out a b : U256) (offset : Nat)
    (hend : offset + 32 ≤ 1024) (hout : 1920 ≤ out.toNat)
    (houtEnd : out.toNat + 32 < 2 ^ 256) :
    loadWord (fp2MulAfterCrossStores yst out a b).memory offset =
      loadWord yst.memory offset := by
  rw [fp2MulAfterCrossStores, fp2MulAfterCrossHigh]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterCrossCall yst out a b).memory 1792
        (fp2MulCross yst out a b).1)
      1824 (fp2MulCross yst out a b).2) offset = _
  rw [loadWord_storeWord_disjoint _ 1824 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1792 offset _ (by omega)]
  unfold fp2MulAfterCrossCall
  rw [fpMulFinalState_loadWord_before_scratch _ _ _ _ _ offset hend]
  exact fp2MulAfterSumBStores_loadWord_before_scratch yst out a b offset hend
    hout houtEnd

private theorem fp2MulAfterVSumStores_loadWord_before_scratch
    (yst : EvmState) (out a b : U256) (offset : Nat)
    (hend : offset + 32 ≤ 1024) (hout : 1920 ≤ out.toNat)
    (houtEnd : out.toNat + 32 < 2 ^ 256) :
    loadWord (fp2MulAfterVSumStores yst out a b).memory offset =
      loadWord yst.memory offset := by
  rw [fp2MulAfterVSumStores, fp2MulAfterVSumHigh]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterCrossStores yst out a b).memory 1856
        (fp2MulVSum yst out a b).1)
      1888 (fp2MulVSum yst out a b).2) offset = _
  rw [loadWord_storeWord_disjoint _ 1888 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1856 offset _ (by omega),
    fp2MulAfterCrossStores_loadWord_before_scratch yst out a b offset hend hout
      houtEnd]

theorem fp2MulFinalState_loadWord_before_scratch
    (yst : EvmState) (out a b : U256) (offset : Nat)
    (hend : offset + 32 ≤ 1024) (hout : 1920 ≤ out.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    loadWord (fp2MulFinalState yst out a b).memory offset =
      loadWord yst.memory offset := by
  rw [fp2MulFinalState, fp2MulAfterImagHigh]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterImagReads yst out a b).memory
        (out + BitVec.ofNat 256 64).toNat (fp2MulImag yst out a b).1)
      (out + BitVec.ofNat 256 96).toNat (fp2MulImag yst out a b).2) offset = _
  rw [loadWord_storeWord_disjoint _
      (out + BitVec.ofNat 256 96).toNat offset _ (by right; bv_omega),
    loadWord_storeWord_disjoint _
      (out + BitVec.ofNat 256 64).toNat offset _ (by right; bv_omega)]
  exact fp2MulAfterVSumStores_loadWord_before_scratch yst out a b offset hend
    hout (by omega)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
