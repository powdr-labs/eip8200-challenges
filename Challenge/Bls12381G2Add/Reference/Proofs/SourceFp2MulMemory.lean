import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulRefinement
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpMulMemory

set_option warningAsError true

/-! # Memory refinement for frozen G2ADD `fp2Mul`

This module proves the scratch read-back facts separately from arithmetic.
That separation is deliberate: expanding both the MODEXP state graph and the
Fp2 source schedule in one theorem causes avoidable elaborator memory growth.
-/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fp2MulAfterV0Stores_load1536 (yst : EvmState) (a b : U256) :
    loadWord (fp2MulAfterV0Stores yst a b).memory 1536 =
      (fp2MulV0 yst a b).1 := by
  rw [fp2MulAfterV0Stores, fp2MulAfterV0High]
  change loadWord
      (storeWord
        (storeWord (fp2MulAfterV0Call yst a b).memory 1536
          (fp2MulV0 yst a b).1)
        1568 (fp2MulV0 yst a b).2) 1536 = _
  rw [loadWord_storeWord_disjoint _ 1568 1536 _ (by omega)]
  rw [loadWord_storeWord_same]

theorem fp2MulAfterV0Stores_load1568 (yst : EvmState) (a b : U256) :
    loadWord (fp2MulAfterV0Stores yst a b).memory 1568 =
      (fp2MulV0 yst a b).2 := by
  rw [fp2MulAfterV0Stores]
  change loadWord
      (storeWord (fp2MulAfterV0High yst a b).memory 1568
        (fp2MulV0 yst a b).2) 1568 = _
  exact loadWord_storeWord_same _ _ _

theorem fp2MulAfterV0Stores_v0 (yst : EvmState) (a b : U256) :
    fpWords (loadWord (fp2MulAfterV0Stores yst a b).memory 1536)
        (loadWord (fp2MulAfterV0Stores yst a b).memory 1568) =
      pairWords (fp2MulV0 yst a b) := by
  rw [fp2MulAfterV0Stores_load1536, fp2MulAfterV0Stores_load1568]
  rfl

theorem fp2MulAfterV1Call_load1536 (yst : EvmState) (a b : U256) :
    loadWord (fp2MulAfterV1Call yst a b).memory 1536 =
      loadWord (fp2MulAfterV0Stores yst a b).memory 1536 := by
  unfold fp2MulAfterV1Call
  rw [fpMulFinalState_loadWord_after_scratch (hstart := by omega)]
  rfl

theorem fp2MulAfterV1Call_load1568 (yst : EvmState) (a b : U256) :
    loadWord (fp2MulAfterV1Call yst a b).memory 1568 =
      loadWord (fp2MulAfterV0Stores yst a b).memory 1568 := by
  unfold fp2MulAfterV1Call
  rw [fpMulFinalState_loadWord_after_scratch (hstart := by omega)]
  rfl

theorem fp2MulAfterV1Stores_v0 (yst : EvmState) (a b : U256) :
    fpWords (loadWord (fp2MulAfterV1Stores yst a b).memory 1536)
        (loadWord (fp2MulAfterV1Stores yst a b).memory 1568) =
      pairWords (fp2MulV0 yst a b) := by
  rw [fp2MulAfterV1Stores, fp2MulAfterV1High]
  change fpWords
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterV1Call yst a b).memory 1600
          (fp2MulV1 yst a b).1)
        1632 (fp2MulV1 yst a b).2) 1536)
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterV1Call yst a b).memory 1600
          (fp2MulV1 yst a b).1)
        1632 (fp2MulV1 yst a b).2) 1568) = _
  rw [loadWord_storeWord_disjoint _ 1632 1536 _ (by omega),
    loadWord_storeWord_disjoint _ 1600 1536 _ (by omega),
    loadWord_storeWord_disjoint _ 1632 1568 _ (by omega),
    loadWord_storeWord_disjoint _ 1600 1568 _ (by omega),
    fp2MulAfterV1Call_load1536, fp2MulAfterV1Call_load1568,
    fp2MulAfterV0Stores_load1536, fp2MulAfterV0Stores_load1568]
  rfl

theorem fp2MulAfterV1Stores_v1 (yst : EvmState) (a b : U256) :
    fpWords (loadWord (fp2MulAfterV1Stores yst a b).memory 1600)
        (loadWord (fp2MulAfterV1Stores yst a b).memory 1632) =
      pairWords (fp2MulV1 yst a b) := by
  rw [fp2MulAfterV1Stores, fp2MulAfterV1High]
  change fpWords
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterV1Call yst a b).memory 1600
          (fp2MulV1 yst a b).1)
        1632 (fp2MulV1 yst a b).2) 1600)
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterV1Call yst a b).memory 1600
          (fp2MulV1 yst a b).1)
        1632 (fp2MulV1 yst a b).2) 1632) = _
  rw [loadWord_storeWord_disjoint _ 1632 1600 _ (by omega),
    loadWord_storeWord_same, loadWord_storeWord_same]
  rfl

theorem fp2MulReal_eq_products (yst : EvmState) (a b : U256) :
    pairWords (fp2MulReal yst a b) =
      Challenge.Bls12381.ProofSupport.Fp.subSource
        (pairWords (fp2MulV0 yst a b)) (pairWords (fp2MulV1 yst a b)) := by
  rw [fp2MulReal_eq_subSource, fp2MulAfterV1Stores_v0,
    fp2MulAfterV1Stores_v1]

theorem fp2MulAfterRealStores_result (yst : EvmState) (out a b : U256)
    (hout : out.toNat + 32 < 2 ^ 256) :
    fpWords
        (loadWord (fp2MulAfterRealStores yst out a b).memory out.toNat)
        (loadWord (fp2MulAfterRealStores yst out a b).memory
          (out + BitVec.ofNat 256 32).toNat) =
      pairWords (fp2MulReal yst a b) := by
  rw [fp2MulAfterRealStores, fp2MulAfterRealHigh]
  change fpWords
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterRealReads yst a b).memory out.toNat
          (fp2MulReal yst a b).1)
        (out + BitVec.ofNat 256 32).toNat (fp2MulReal yst a b).2) out.toNat)
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterRealReads yst a b).memory out.toNat
          (fp2MulReal yst a b).1)
        (out + BitVec.ofNat 256 32).toNat (fp2MulReal yst a b).2)
      (out + BitVec.ofNat 256 32).toNat) = _
  rw [loadWord_storeWord_same]
  have hoff : (out + BitVec.ofNat 256 32).toNat = out.toNat + 32 := by
    bv_omega
  rw [hoff, loadWord_storeWord_disjoint _ (out.toNat + 32) out.toNat _
    (by omega), loadWord_storeWord_same]
  rfl

theorem fp2MulAfterSumAStores_sumA (yst : EvmState) (out a b : U256) :
    fpWords (loadWord (fp2MulAfterSumAStores yst out a b).memory 1664)
        (loadWord (fp2MulAfterSumAStores yst out a b).memory 1696) =
      pairWords (fp2MulSumA yst out a b) := by
  rw [fp2MulAfterSumAStores, fp2MulAfterSumAHigh]
  change fpWords
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterSumAReads yst out a b).memory 1664
          (fp2MulSumA yst out a b).1)
        1696 (fp2MulSumA yst out a b).2) 1664)
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterSumAReads yst out a b).memory 1664
          (fp2MulSumA yst out a b).1)
        1696 (fp2MulSumA yst out a b).2) 1696) = _
  rw [loadWord_storeWord_disjoint _ 1696 1664 _ (by omega),
    loadWord_storeWord_same, loadWord_storeWord_same]
  rfl

theorem fp2MulAfterSumBStores_sumA (yst : EvmState) (out a b : U256) :
    fpWords (loadWord (fp2MulAfterSumBStores yst out a b).memory 1664)
        (loadWord (fp2MulAfterSumBStores yst out a b).memory 1696) =
      pairWords (fp2MulSumA yst out a b) := by
  rw [fp2MulAfterSumBStores, fp2MulAfterSumBHigh]
  change fpWords
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterSumAStores yst out a b).memory 1728
          (fp2MulSumB yst out a b).1)
        1760 (fp2MulSumB yst out a b).2) 1664)
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterSumAStores yst out a b).memory 1728
          (fp2MulSumB yst out a b).1)
        1760 (fp2MulSumB yst out a b).2) 1696) = _
  rw [loadWord_storeWord_disjoint _ 1760 1664 _ (by omega),
    loadWord_storeWord_disjoint _ 1728 1664 _ (by omega),
    loadWord_storeWord_disjoint _ 1760 1696 _ (by omega),
    loadWord_storeWord_disjoint _ 1728 1696 _ (by omega),
    fp2MulAfterSumAStores_sumA]

theorem fp2MulAfterSumBStores_sumB (yst : EvmState) (out a b : U256) :
    fpWords (loadWord (fp2MulAfterSumBStores yst out a b).memory 1728)
        (loadWord (fp2MulAfterSumBStores yst out a b).memory 1760) =
      pairWords (fp2MulSumB yst out a b) := by
  rw [fp2MulAfterSumBStores, fp2MulAfterSumBHigh]
  change fpWords
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterSumAStores yst out a b).memory 1728
          (fp2MulSumB yst out a b).1)
        1760 (fp2MulSumB yst out a b).2) 1728)
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterSumAStores yst out a b).memory 1728
          (fp2MulSumB yst out a b).1)
        1760 (fp2MulSumB yst out a b).2) 1760) = _
  rw [loadWord_storeWord_disjoint _ 1760 1728 _ (by omega),
    loadWord_storeWord_same, loadWord_storeWord_same]
  rfl

theorem fp2MulCross_inputs (yst : EvmState) (out a b : U256) :
    fp2MulCrossLeft yst out a b = pairWords (fp2MulSumA yst out a b) ∧
      fp2MulCrossRight yst out a b = pairWords (fp2MulSumB yst out a b) := by
  exact ⟨fp2MulAfterSumBStores_sumA yst out a b,
    fp2MulAfterSumBStores_sumB yst out a b⟩

theorem fp2MulCross_eq_sums (yst : EvmState) (out a b : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (pairWords (fp2MulSumA yst out a b)))
    (hb : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (pairWords (fp2MulSumB yst out a b))) :
    pairWords (fp2MulCross yst out a b) =
      Challenge.Bls12381.ProofSupport.Fp.mulCanonical
        (pairWords (fp2MulSumA yst out a b))
        (pairWords (fp2MulSumB yst out a b)) := by
  have hinputs := fp2MulCross_inputs yst out a b
  rw [fp2MulCross_eq_mulCanonical _ _ _ _
    (hinputs.1 ▸ ha) (hinputs.2 ▸ hb), hinputs.1, hinputs.2]

theorem fp2MulAfterCrossStores_cross (yst : EvmState) (out a b : U256) :
    fpWords (loadWord (fp2MulAfterCrossStores yst out a b).memory 1792)
        (loadWord (fp2MulAfterCrossStores yst out a b).memory 1824) =
      pairWords (fp2MulCross yst out a b) := by
  rw [fp2MulAfterCrossStores, fp2MulAfterCrossHigh]
  change fpWords
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterCrossCall yst out a b).memory 1792
          (fp2MulCross yst out a b).1)
        1824 (fp2MulCross yst out a b).2) 1792)
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterCrossCall yst out a b).memory 1792
          (fp2MulCross yst out a b).1)
        1824 (fp2MulCross yst out a b).2) 1824) = _
  rw [loadWord_storeWord_disjoint _ 1824 1792 _ (by omega),
    loadWord_storeWord_same, loadWord_storeWord_same]
  rfl

theorem fp2MulAfterVSumStores_cross (yst : EvmState) (out a b : U256) :
    fpWords (loadWord (fp2MulAfterVSumStores yst out a b).memory 1792)
        (loadWord (fp2MulAfterVSumStores yst out a b).memory 1824) =
      pairWords (fp2MulCross yst out a b) := by
  rw [fp2MulAfterVSumStores, fp2MulAfterVSumHigh]
  change fpWords
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterCrossStores yst out a b).memory 1856
          (fp2MulVSum yst out a b).1)
        1888 (fp2MulVSum yst out a b).2) 1792)
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterCrossStores yst out a b).memory 1856
          (fp2MulVSum yst out a b).1)
        1888 (fp2MulVSum yst out a b).2) 1824) = _
  rw [loadWord_storeWord_disjoint _ 1888 1792 _ (by omega),
    loadWord_storeWord_disjoint _ 1856 1792 _ (by omega),
    loadWord_storeWord_disjoint _ 1888 1824 _ (by omega),
    loadWord_storeWord_disjoint _ 1856 1824 _ (by omega),
    fp2MulAfterCrossStores_cross]

theorem fp2MulAfterVSumStores_vsum (yst : EvmState) (out a b : U256) :
    fpWords (loadWord (fp2MulAfterVSumStores yst out a b).memory 1856)
        (loadWord (fp2MulAfterVSumStores yst out a b).memory 1888) =
      pairWords (fp2MulVSum yst out a b) := by
  rw [fp2MulAfterVSumStores, fp2MulAfterVSumHigh]
  change fpWords
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterCrossStores yst out a b).memory 1856
          (fp2MulVSum yst out a b).1)
        1888 (fp2MulVSum yst out a b).2) 1856)
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterCrossStores yst out a b).memory 1856
          (fp2MulVSum yst out a b).1)
        1888 (fp2MulVSum yst out a b).2) 1888) = _
  rw [loadWord_storeWord_disjoint _ 1888 1856 _ (by omega),
    loadWord_storeWord_same, loadWord_storeWord_same]
  rfl

theorem fp2MulImag_eq_cross_vsum (yst : EvmState) (out a b : U256) :
    pairWords (fp2MulImag yst out a b) =
      Challenge.Bls12381.ProofSupport.Fp.subSource
        (pairWords (fp2MulCross yst out a b))
        (pairWords (fp2MulVSum yst out a b)) := by
  rw [fp2MulImag_eq_subSource, fp2MulAfterVSumStores_cross,
    fp2MulAfterVSumStores_vsum]

theorem fp2MulAfterSumAStores_loadWord_high (yst : EvmState) (out a b : U256)
    (offset : Nat) (hoffset : 1728 ≤ offset) :
    loadWord (fp2MulAfterSumAStores yst out a b).memory offset =
      loadWord (fp2MulAfterRealStores yst out a b).memory offset := by
  rw [fp2MulAfterSumAStores, fp2MulAfterSumAHigh]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterRealStores yst out a b).memory 1664
        (fp2MulSumA yst out a b).1)
      1696 (fp2MulSumA yst out a b).2) offset = _
  rw [loadWord_storeWord_disjoint _ 1696 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1664 offset _ (by omega)]

theorem fp2MulAfterSumBStores_loadWord_high (yst : EvmState) (out a b : U256)
    (offset : Nat) (hoffset : 1792 ≤ offset) :
    loadWord (fp2MulAfterSumBStores yst out a b).memory offset =
      loadWord (fp2MulAfterRealStores yst out a b).memory offset := by
  rw [fp2MulAfterSumBStores, fp2MulAfterSumBHigh]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterSumAStores yst out a b).memory 1728
        (fp2MulSumB yst out a b).1)
      1760 (fp2MulSumB yst out a b).2) offset = _
  rw [loadWord_storeWord_disjoint _ 1760 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1728 offset _ (by omega),
    fp2MulAfterSumAStores_loadWord_high _ _ _ _ offset (by omega)]

theorem fp2MulAfterCrossStores_loadWord_high (yst : EvmState) (out a b : U256)
    (offset : Nat) (hoffset : 1856 ≤ offset) :
    loadWord (fp2MulAfterCrossStores yst out a b).memory offset =
      loadWord (fp2MulAfterRealStores yst out a b).memory offset := by
  rw [fp2MulAfterCrossStores, fp2MulAfterCrossHigh]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterCrossCall yst out a b).memory 1792
        (fp2MulCross yst out a b).1)
      1824 (fp2MulCross yst out a b).2) offset = _
  rw [loadWord_storeWord_disjoint _ 1824 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1792 offset _ (by omega)]
  unfold fp2MulAfterCrossCall
  rw [fpMulFinalState_loadWord_after_scratch (hstart := by omega)]
  have hreads : (fp2MulAfterCrossReads yst out a b).memory =
      (fp2MulAfterSumBStores yst out a b).memory := rfl
  rw [hreads,
    fp2MulAfterSumBStores_loadWord_high _ _ _ _ offset (by omega)]

theorem fp2MulAfterVSumStores_loadWord_high (yst : EvmState) (out a b : U256)
    (offset : Nat) (hoffset : 1920 ≤ offset) :
    loadWord (fp2MulAfterVSumStores yst out a b).memory offset =
      loadWord (fp2MulAfterRealStores yst out a b).memory offset := by
  rw [fp2MulAfterVSumStores, fp2MulAfterVSumHigh]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterCrossStores yst out a b).memory 1856
        (fp2MulVSum yst out a b).1)
      1888 (fp2MulVSum yst out a b).2) offset = _
  rw [loadWord_storeWord_disjoint _ 1888 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1856 offset _ (by omega),
    fp2MulAfterCrossStores_loadWord_high _ _ _ _ offset (by omega)]

theorem fp2MulFinalState_c1 (yst : EvmState) (out a b : U256)
    (hout : out.toNat + 96 < 2 ^ 256) :
    (fp2At (fp2MulFinalState yst out a b) out).c1 =
      pairWords (fp2MulImag yst out a b) := by
  have h64 : (out + BitVec.ofNat 256 64).toNat = out.toNat + 64 := by
    bv_omega
  have h96 : (out + BitVec.ofNat 256 96).toNat = out.toNat + 96 := by
    bv_omega
  rw [fp2MulFinalState, fp2MulAfterImagHigh]
  change fpWords
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterImagReads yst out a b).memory
          (out + BitVec.ofNat 256 64).toNat (fp2MulImag yst out a b).1)
        (out + BitVec.ofNat 256 96).toNat (fp2MulImag yst out a b).2)
      (out + BitVec.ofNat 256 64).toNat)
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterImagReads yst out a b).memory
          (out + BitVec.ofNat 256 64).toNat (fp2MulImag yst out a b).1)
        (out + BitVec.ofNat 256 96).toNat (fp2MulImag yst out a b).2)
      (out + BitVec.ofNat 256 96).toNat) = _
  rw [h64, h96,
    loadWord_storeWord_disjoint _ (out.toNat + 96) (out.toNat + 64) _
      (by omega),
    loadWord_storeWord_same, loadWord_storeWord_same]
  rfl

theorem fp2MulFinalState_c0 (yst : EvmState) (out a b : U256)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    (fp2At (fp2MulFinalState yst out a b) out).c0 =
      pairWords (fp2MulReal yst a b) := by
  have h32 : (out + BitVec.ofNat 256 32).toNat = out.toNat + 32 := by
    bv_omega
  have h64 : (out + BitVec.ofNat 256 64).toNat = out.toNat + 64 := by
    bv_omega
  have h96 : (out + BitVec.ofNat 256 96).toNat = out.toNat + 96 := by
    bv_omega
  rw [fp2MulFinalState, fp2MulAfterImagHigh]
  change fpWords
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterImagReads yst out a b).memory
          (out + BitVec.ofNat 256 64).toNat (fp2MulImag yst out a b).1)
        (out + BitVec.ofNat 256 96).toNat (fp2MulImag yst out a b).2)
      out.toNat)
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterImagReads yst out a b).memory
          (out + BitVec.ofNat 256 64).toNat (fp2MulImag yst out a b).1)
        (out + BitVec.ofNat 256 96).toNat (fp2MulImag yst out a b).2)
      (out + BitVec.ofNat 256 32).toNat) = _
  rw [h32, h64, h96,
    loadWord_storeWord_disjoint _ (out.toNat + 96) out.toNat _ (by omega),
    loadWord_storeWord_disjoint _ (out.toNat + 64) out.toNat _ (by omega),
    loadWord_storeWord_disjoint _ (out.toNat + 96) (out.toNat + 32) _
      (by omega),
    loadWord_storeWord_disjoint _ (out.toNat + 64) (out.toNat + 32) _
      (by omega)]
  have hreads : (fp2MulAfterImagReads yst out a b).memory =
      (fp2MulAfterVSumStores yst out a b).memory := rfl
  rw [hreads,
    fp2MulAfterVSumStores_loadWord_high _ _ _ _ out.toNat houtHigh,
    fp2MulAfterVSumStores_loadWord_high _ _ _ _ (out.toNat + 32)
      (by omega)]
  simpa [h32] using fp2MulAfterRealStores_result yst out a b (by omega)

theorem fp2MulAfterRealStores_loadProduct (yst : EvmState) (out a b : U256)
    (offset : Nat) (hend : offset + 32 ≤ 1664)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 32 < 2 ^ 256) :
    loadWord (fp2MulAfterRealStores yst out a b).memory offset =
      loadWord (fp2MulAfterV1Stores yst a b).memory offset := by
  have h32 : (out + BitVec.ofNat 256 32).toNat = out.toNat + 32 := by
    bv_omega
  rw [fp2MulAfterRealStores, fp2MulAfterRealHigh]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterRealReads yst a b).memory out.toNat
        (fp2MulReal yst a b).1)
      (out + BitVec.ofNat 256 32).toNat (fp2MulReal yst a b).2) offset = _
  rw [h32,
    loadWord_storeWord_disjoint _ (out.toNat + 32) offset _ (by omega),
    loadWord_storeWord_disjoint _ out.toNat offset _ (by omega)]
  rfl

theorem fp2MulAfterSumBStores_loadProduct (yst : EvmState) (out a b : U256)
    (offset : Nat) (hend : offset + 32 ≤ 1664)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 32 < 2 ^ 256) :
    loadWord (fp2MulAfterSumBStores yst out a b).memory offset =
      loadWord (fp2MulAfterV1Stores yst a b).memory offset := by
  rw [fp2MulAfterSumBStores, fp2MulAfterSumBHigh]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterSumAStores yst out a b).memory 1728
        (fp2MulSumB yst out a b).1)
      1760 (fp2MulSumB yst out a b).2) offset = _
  rw [loadWord_storeWord_disjoint _ 1760 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1728 offset _ (by omega)]
  rw [fp2MulAfterSumAStores, fp2MulAfterSumAHigh]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterRealStores yst out a b).memory 1664
        (fp2MulSumA yst out a b).1)
      1696 (fp2MulSumA yst out a b).2) offset = _
  rw [loadWord_storeWord_disjoint _ 1696 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1664 offset _ (by omega),
    fp2MulAfterRealStores_loadProduct _ _ _ _ offset hend houtHigh hout]

theorem fp2MulAfterCrossStores_loadProduct (yst : EvmState) (out a b : U256)
    (offset : Nat) (hstart : 1328 ≤ offset) (hend : offset + 32 ≤ 1664)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 32 < 2 ^ 256) :
    loadWord (fp2MulAfterCrossStores yst out a b).memory offset =
      loadWord (fp2MulAfterV1Stores yst a b).memory offset := by
  rw [fp2MulAfterCrossStores, fp2MulAfterCrossHigh]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterCrossCall yst out a b).memory 1792
        (fp2MulCross yst out a b).1)
      1824 (fp2MulCross yst out a b).2) offset = _
  rw [loadWord_storeWord_disjoint _ 1824 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1792 offset _ (by omega)]
  unfold fp2MulAfterCrossCall
  rw [fpMulFinalState_loadWord_after_scratch (hstart := hstart)]
  have hreads : (fp2MulAfterCrossReads yst out a b).memory =
      (fp2MulAfterSumBStores yst out a b).memory := rfl
  rw [hreads,
    fp2MulAfterSumBStores_loadProduct _ _ _ _ offset hend houtHigh hout]

theorem fp2MulAfterCrossStores_products (yst : EvmState) (out a b : U256)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 32 < 2 ^ 256) :
    fpWords (loadWord (fp2MulAfterCrossStores yst out a b).memory 1536)
        (loadWord (fp2MulAfterCrossStores yst out a b).memory 1568) =
        pairWords (fp2MulV0 yst a b) ∧
      fpWords (loadWord (fp2MulAfterCrossStores yst out a b).memory 1600)
        (loadWord (fp2MulAfterCrossStores yst out a b).memory 1632) =
        pairWords (fp2MulV1 yst a b) := by
  constructor
  · rw [fp2MulAfterCrossStores_loadProduct _ _ _ _ 1536 (by omega)
      (by omega) houtHigh hout,
    fp2MulAfterCrossStores_loadProduct _ _ _ _ 1568 (by omega)
      (by omega) houtHigh hout,
    fp2MulAfterV1Stores_v0]
  · rw [fp2MulAfterCrossStores_loadProduct _ _ _ _ 1600 (by omega)
      (by omega) houtHigh hout,
    fp2MulAfterCrossStores_loadProduct _ _ _ _ 1632 (by omega)
      (by omega) houtHigh hout,
    fp2MulAfterV1Stores_v1]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
