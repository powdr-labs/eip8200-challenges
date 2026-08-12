import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvRefinement
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpInvMemory
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpMulMemory

set_option warningAsError true
/-! # Memory refinement for frozen G2ADD `fp2Inv` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
open YulSemantics
open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem fp2InvAfterSquare0Stores_square0 (yst : EvmState) (a : U256) :
    fpWords (loadWord (fp2InvAfterSquare0Stores yst a).memory 1536)
        (loadWord (fp2InvAfterSquare0Stores yst a).memory 1568) =
      pairWords (fp2InvSquare0 yst a) := by
  rw [fp2InvAfterSquare0Stores, fp2InvAfterSquare0High]
  change fpWords
    (loadWord (storeWord
      (storeWord (fp2InvAfterSquare0Call yst a).memory 1536
        (fp2InvSquare0 yst a).1) 1568 (fp2InvSquare0 yst a).2) 1536)
    (loadWord (storeWord
      (storeWord (fp2InvAfterSquare0Call yst a).memory 1536
        (fp2InvSquare0 yst a).1) 1568 (fp2InvSquare0 yst a).2) 1568) = _
  rw [loadWord_storeWord_disjoint _ 1568 1536 _ (by omega),
    loadWord_storeWord_same, loadWord_storeWord_same]
  rfl

theorem fp2InvAfterSquare1Stores_square0 (yst : EvmState) (a : U256) :
    fpWords (loadWord (fp2InvAfterSquare1Stores yst a).memory 1536)
        (loadWord (fp2InvAfterSquare1Stores yst a).memory 1568) =
      pairWords (fp2InvSquare0 yst a) := by
  rw [fp2InvAfterSquare1Stores, fp2InvAfterSquare1High]
  change fpWords
    (loadWord (storeWord
      (storeWord (fp2InvAfterSquare1Call yst a).memory 1600
        (fp2InvSquare1 yst a).1) 1632 (fp2InvSquare1 yst a).2) 1536)
    (loadWord (storeWord
      (storeWord (fp2InvAfterSquare1Call yst a).memory 1600
        (fp2InvSquare1 yst a).1) 1632 (fp2InvSquare1 yst a).2) 1568) = _
  rw [loadWord_storeWord_disjoint _ 1632 1536 _ (by omega),
    loadWord_storeWord_disjoint _ 1600 1536 _ (by omega),
    loadWord_storeWord_disjoint _ 1632 1568 _ (by omega),
    loadWord_storeWord_disjoint _ 1600 1568 _ (by omega)]
  unfold fp2InvAfterSquare1Call
  rw [fpMulFinalState_loadWord_after_scratch (hstart := by omega),
    fpMulFinalState_loadWord_after_scratch (hstart := by omega)]
  change fpWords
    (loadWord (fp2InvAfterSquare0Stores yst a).memory 1536)
    (loadWord (fp2InvAfterSquare0Stores yst a).memory 1568) = _
  exact fp2InvAfterSquare0Stores_square0 yst a

theorem fp2InvAfterSquare1Stores_square1 (yst : EvmState) (a : U256) :
    fpWords (loadWord (fp2InvAfterSquare1Stores yst a).memory 1600)
        (loadWord (fp2InvAfterSquare1Stores yst a).memory 1632) =
      pairWords (fp2InvSquare1 yst a) := by
  rw [fp2InvAfterSquare1Stores, fp2InvAfterSquare1High]
  change fpWords
    (loadWord (storeWord
      (storeWord (fp2InvAfterSquare1Call yst a).memory 1600
        (fp2InvSquare1 yst a).1) 1632 (fp2InvSquare1 yst a).2) 1600)
    (loadWord (storeWord
      (storeWord (fp2InvAfterSquare1Call yst a).memory 1600
        (fp2InvSquare1 yst a).1) 1632 (fp2InvSquare1 yst a).2) 1632) = _
  rw [loadWord_storeWord_disjoint _ 1632 1600 _ (by omega),
    loadWord_storeWord_same, loadWord_storeWord_same]
  rfl

theorem fp2InvAfterSquare0Stores_loadWord_high (yst : EvmState) (a : U256)
    (offset : Nat) (hstart : 1600 ≤ offset) :
    loadWord (fp2InvAfterSquare0Stores yst a).memory offset =
      loadWord yst.memory offset := by
  rw [fp2InvAfterSquare0Stores, fp2InvAfterSquare0High]
  change loadWord
    (storeWord
      (storeWord (fp2InvAfterSquare0Call yst a).memory 1536
        (fp2InvSquare0 yst a).1)
      1568 (fp2InvSquare0 yst a).2) offset = _
  rw [loadWord_storeWord_disjoint _ 1568 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1536 offset _ (by omega)]
  unfold fp2InvAfterSquare0Call
  rw [fpMulFinalState_loadWord_after_scratch (hstart := by omega)]
  rfl

theorem fp2InvAfterSquare1Stores_loadWord_high (yst : EvmState) (a : U256)
    (offset : Nat) (hstart : 1664 ≤ offset) :
    loadWord (fp2InvAfterSquare1Stores yst a).memory offset =
      loadWord yst.memory offset := by
  rw [fp2InvAfterSquare1Stores, fp2InvAfterSquare1High]
  change loadWord
    (storeWord
      (storeWord (fp2InvAfterSquare1Call yst a).memory 1600
        (fp2InvSquare1 yst a).1)
      1632 (fp2InvSquare1 yst a).2) offset = _
  rw [loadWord_storeWord_disjoint _ 1632 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1600 offset _ (by omega)]
  unfold fp2InvAfterSquare1Call
  rw [fpMulFinalState_loadWord_after_scratch (hstart := by omega)]
  rw [fp2InvAfterSquare1Reads, fp2AddReadState_memory]
  exact fp2InvAfterSquare0Stores_loadWord_high yst a offset (by omega)

theorem fp2InvAfterScalarStores_scalar (yst : EvmState) (a : U256) :
    fp2InvScalarStored yst a = pairWords (fp2InvScalar yst a) := by
  rw [fp2InvScalarStored, fp2InvAfterScalarStores, fp2InvAfterScalarHigh]
  change fpWords
    (loadWord
      (storeWord
        (storeWord (fp2InvAfterScalarCall yst a).memory 1664
          (fp2InvScalar yst a).1)
        1696 (fp2InvScalar yst a).2) 1664)
    (loadWord
      (storeWord
        (storeWord (fp2InvAfterScalarCall yst a).memory 1664
          (fp2InvScalar yst a).1)
        1696 (fp2InvScalar yst a).2) 1696) = _
  rw [loadWord_storeWord_disjoint _ 1696 1664 _ (by omega),
    loadWord_storeWord_same, loadWord_storeWord_same]
  rfl

theorem fp2InvAfterScalarStores_loadWord_high (yst : EvmState) (a : U256)
    (offset : Nat) (hstart : 1728 ≤ offset) :
    loadWord (fp2InvAfterScalarStores yst a).memory offset =
      loadWord yst.memory offset := by
  rw [fp2InvAfterScalarStores, fp2InvAfterScalarHigh]
  change loadWord
    (storeWord
      (storeWord (fp2InvAfterScalarCall yst a).memory 1664
        (fp2InvScalar yst a).1)
      1696 (fp2InvScalar yst a).2) offset = _
  rw [loadWord_storeWord_disjoint _ 1696 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1664 offset _ (by omega)]
  unfold fp2InvAfterScalarCall
  rw [fpInvFinalState_loadWord_after_scratch (hstart := by omega)]
  rw [fp2InvAfterNormReads, fp2AddReadState_memory]
  exact fp2InvAfterSquare1Stores_loadWord_high yst a offset (by omega)

theorem fp2InvNorm_eq_squares (yst : EvmState) (a : U256) :
    pairWords (fp2InvNorm yst a) =
      Fp.addSource (pairWords (fp2InvSquare0 yst a))
        (pairWords (fp2InvSquare1 yst a)) := by
  rw [fp2InvNorm_eq_addSource, fp2InvAfterSquare1Stores_square0,
    fp2InvAfterSquare1Stores_square1]

theorem fp2InvNorm_canonical (yst : EvmState) (a : U256)
    (h0 : Fp.Canonical (pairWords (fp2InvSquare0 yst a)))
    (h1 : Fp.Canonical (pairWords (fp2InvSquare1 yst a))) :
    Fp.Canonical (pairWords (fp2InvNorm yst a)) := by
  rw [fp2InvNorm_eq_squares]
  exact Fp.canonical_addSource h0 h1

theorem fp2InvNorm_hi_lt (yst : EvmState) (a : U256)
    (h0 : Fp.Canonical (pairWords (fp2InvSquare0 yst a)))
    (h1 : Fp.Canonical (pairWords (fp2InvSquare1 yst a))) :
    (fp2InvNorm yst a).1.toNat < 2 ^ 128 :=
  (fp2InvNorm_canonical yst a h0 h1).1

theorem fp2InvSquare1Input_eq (yst : EvmState) (a : U256)
    (haHigh : 1920 ≤ a.toNat) (ha : a.toNat + 96 < 2 ^ 256) :
    fp2InvSquare1Input yst a = (fp2At yst a).c1 := by
  have h64 : (a + BitVec.ofNat 256 64).toNat = a.toNat + 64 := by
    bv_omega
  have h96 : (a + BitVec.ofNat 256 96).toNat = a.toNat + 96 := by
    bv_omega
  rw [fp2InvSquare1Input, h64, h96,
    fp2InvAfterSquare0Stores_loadWord_high _ _ (a.toNat + 64) (by omega),
    fp2InvAfterSquare0Stores_loadWord_high _ _ (a.toNat + 96) (by omega)]
  change fpWords (loadWord yst.memory (a.toNat + 64))
    (loadWord yst.memory (a.toNat + 96)) =
    fpWords (loadWord yst.memory (a + BitVec.ofNat 256 64).toNat)
      (loadWord yst.memory (a + BitVec.ofNat 256 96).toNat)
  rw [h64, h96]

theorem fp2InvSquares_canonical (yst : EvmState) (a : U256)
    (haCanonical : Fp2.Canonical (fp2At yst a))
    (haHigh : 1920 ≤ a.toNat) (ha : a.toNat + 96 < 2 ^ 256) :
    Fp.Canonical (pairWords (fp2InvSquare0 yst a)) ∧
      Fp.Canonical (pairWords (fp2InvSquare1 yst a)) := by
  constructor
  · rw [fp2InvSquare0_eq_mulCanonical yst a haCanonical.c0.proof]
    exact Fp.canonical_mulCanonical haCanonical.c0.proof haCanonical.c0.proof
  · have hinput : Fp.Canonical (fp2InvSquare1Input yst a) := by
      rw [fp2InvSquare1Input_eq yst a haHigh ha]
      exact haCanonical.c1.proof
    rw [fp2InvSquare1_eq_mulCanonical yst a hinput]
    exact Fp.canonical_mulCanonical hinput hinput

theorem fp2InvNorm_hi_lt_of_input (yst : EvmState) (a : U256)
    (haCanonical : Fp2.Canonical (fp2At yst a))
    (haHigh : 1920 ≤ a.toNat) (ha : a.toNat + 96 < 2 ^ 256) :
    (fp2InvNorm yst a).1.toNat < 2 ^ 128 := by
  have hs := fp2InvSquares_canonical yst a haCanonical haHigh ha
  exact fp2InvNorm_hi_lt yst a hs.1 hs.2

theorem step_fp2Inv_of_input (yst : EvmState) (out a : U256)
    (haCanonical : Fp2.Canonical (fp2At yst a))
    (haHigh : 1920 ≤ a.toNat) (ha : a.toNat + 96 < 2 ^ 256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect fp2InvFuns
      [("out", out), ("a", a)] yst
      (.call "\x0017" [.var "out", .var "a"])
      (.vals [] (fp2InvFinalState yst out a)) :=
  step_fp2Inv yst out a
    (fp2InvNorm_hi_lt_of_input yst a haCanonical haHigh ha)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
