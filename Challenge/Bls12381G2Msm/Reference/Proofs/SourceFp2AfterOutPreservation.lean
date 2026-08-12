import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointMemory
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddPreservation
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2SubPreservation
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulHighInputs
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulHighLawful
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulBeforeOutLawful
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvPreservation

set_option warningAsError true

/-!
High-cell preservation needed by the fixed G2MSM layout.

G2ADD mostly consumes operands below its output, whereas G2MSM deliberately
keeps point cells above all arithmetic scratch.  These are the symmetric
after-output memory facts; they keep that layout choice out of arithmetic
refinement proofs.
-/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

/-- The locally staged multiplication state is definitionally the approved
G2ADD arithmetic graph; only the source identifiers differ. -/
theorem fp2MulFinalState_eq_shared (yst : EvmState) (out a b : U256) :
    fp2MulFinalState yst out a b =
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulFinalState
        yst out a b := by
  rfl

theorem fp2MulFinalState_canonical_after (yst : EvmState)
    (out a b : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst a))
    (hb : Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst b))
    (haEnd : a.toNat + 96 < 2 ^ 256) (haHigh : 1664 ≤ a.toNat)
    (haAfter : out.toNat + 64 ≤ a.toNat)
    (hbEnd : b.toNat + 96 < 2 ^ 256) (hbHigh : 1728 ≤ b.toNat)
    (hbAfter : out.toNat + 64 ≤ b.toNat)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    Challenge.Bls12381.ProofSupport.Fp2.Canonical
      (fp2At (fp2MulFinalState yst out a b) out) := by
  rw [fp2MulFinalState_eq_shared]
  exact fp2MulFinalState_canonical_of_high_after_out yst out a b ha hb
    haEnd haHigh haAfter hbEnd hbHigh hbAfter houtHigh hout

theorem fp2MulFinalState_toLawful_after (yst : EvmState)
    (out a b : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst a))
    (hb : Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst b))
    (haEnd : a.toNat + 96 < 2 ^ 256) (haHigh : 1664 ≤ a.toNat)
    (haAfter : out.toNat + 64 ≤ a.toNat)
    (hbEnd : b.toNat + 96 < 2 ^ 256) (hbHigh : 1728 ≤ b.toNat)
    (hbAfter : out.toNat + 64 ≤ b.toNat)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    Challenge.Bls12381.ProofSupport.Fp2.toLawful
        (fp2At (fp2MulFinalState yst out a b) out) =
      Challenge.Bls12381.ProofSupport.Fp2.toLawful (fp2At yst a) *
        Challenge.Bls12381.ProofSupport.Fp2.toLawful (fp2At yst b) := by
  rw [fp2MulFinalState_eq_shared]
  exact fp2MulFinalState_toLawful_mul_of_high_after_out yst out a b ha hb
    haEnd haHigh haAfter hbEnd hbHigh hbAfter houtHigh hout

theorem fp2MulFinalState_canonical_before (yst : EvmState)
    (out a b : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst a))
    (hb : Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst b))
    (haEnd : a.toNat + 96 < 2 ^ 256) (haHigh : 1664 ≤ a.toNat)
    (haBefore : a.toNat + 128 ≤ out.toNat)
    (hbEnd : b.toNat + 96 < 2 ^ 256) (hbHigh : 1728 ≤ b.toNat)
    (hbBefore : b.toNat + 128 ≤ out.toNat)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    Challenge.Bls12381.ProofSupport.Fp2.Canonical
      (fp2At (fp2MulFinalState yst out a b) out) := by
  rw [fp2MulFinalState_eq_shared]
  exact fp2MulFinalState_canonical_of_high_before_out yst out a b ha hb
    haEnd haHigh haBefore hbEnd hbHigh hbBefore houtHigh hout

theorem fp2MulFinalState_toLawful_before (yst : EvmState)
    (out a b : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst a))
    (hb : Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst b))
    (haEnd : a.toNat + 96 < 2 ^ 256) (haHigh : 1664 ≤ a.toNat)
    (haBefore : a.toNat + 128 ≤ out.toNat)
    (hbEnd : b.toNat + 96 < 2 ^ 256) (hbHigh : 1728 ≤ b.toNat)
    (hbBefore : b.toNat + 128 ≤ out.toNat)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    Challenge.Bls12381.ProofSupport.Fp2.toLawful
        (fp2At (fp2MulFinalState yst out a b) out) =
      Challenge.Bls12381.ProofSupport.Fp2.toLawful (fp2At yst a) *
        Challenge.Bls12381.ProofSupport.Fp2.toLawful (fp2At yst b) := by
  rw [fp2MulFinalState_eq_shared]
  exact fp2MulFinalState_toLawful_mul_of_high_before_out yst out a b ha hb
    haEnd haHigh haBefore hbEnd hbHigh hbBefore houtHigh hout

theorem fp2AddFinalState_fp2At_after_out (yst : EvmState)
    (out a b ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hafter : out.toNat + 128 ≤ ptr.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    fp2At (fp2AddFinalState yst out a b) ptr = fp2At yst ptr := by
  apply fp2At_eq_of_loads
  all_goals
    unfold fp2AddFinalState
    unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddFinalState
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddAfterC1High
    change loadWord
      (storeWord (storeWord (fp2AddAfterC1Reads yst out a b).memory
        (out + BitVec.ofNat 256 64).toNat _)
        (out + BitVec.ofNat 256 96).toNat _) _ = _
    rw [loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega),
      loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega)]
    have hreads : (fp2AddAfterC1Reads yst out a b).memory =
        (fp2AddAfterC0Stores yst out a b).memory := rfl
    rw [hreads]
    unfold fp2AddAfterC0Stores
    unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddAfterC0Stores
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddAfterC0High
    change loadWord (storeWord (storeWord yst.memory out.toNat _)
      (out + BitVec.ofNat 256 32).toNat _) _ = _
    rw [loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega),
      loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega)]

theorem fp2SubFinalState_fp2At_after_out (yst : EvmState)
    (out a b ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hafter : out.toNat + 128 ≤ ptr.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    fp2At (fp2SubFinalState yst out a b) ptr = fp2At yst ptr := by
  apply fp2At_eq_of_loads
  all_goals
    unfold fp2SubFinalState
    unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubFinalState
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubAfterC1High
    change loadWord
      (storeWord (storeWord (fp2SubAfterC1Reads yst out a b).memory
        (out + BitVec.ofNat 256 64).toNat _)
        (out + BitVec.ofNat 256 96).toNat _) _ = _
    rw [loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega),
      loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega)]
    have hreads : (fp2SubAfterC1Reads yst out a b).memory =
        (fp2SubAfterC0Stores yst out a b).memory := rfl
    rw [hreads]
    unfold fp2SubAfterC0Stores
    unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubAfterC0Stores
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubAfterC0High
    change loadWord (storeWord (storeWord yst.memory out.toNat _)
      (out + BitVec.ofNat 256 32).toNat _) _ = _
    rw [loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega),
      loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega)]

private theorem fp2SubAfterC0Stores_fp2At_after_out (yst : EvmState)
    (out a b ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hafter : out.toNat + 64 ≤ ptr.toNat)
    (houtEnd : out.toNat + 32 < 2 ^ 256) :
    fp2At (fp2SubAfterC0Stores yst out a b) ptr = fp2At yst ptr := by
  apply fp2At_eq_of_loads
  all_goals
    unfold fp2SubAfterC0Stores
    unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubAfterC0Stores
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubAfterC0High
    change loadWord
      (storeWord
        (storeWord
          (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubAfterC0Reads
            yst a b).memory out.toNat _)
        (out + BitVec.ofNat 256 32).toNat _) _ = _
    rw [loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega),
      loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega)]
    rfl

theorem fp2SubScheduledA_eq_after_out (yst : EvmState) (out a b : U256)
    (haEnd : a.toNat + 96 < 2 ^ 256)
    (haAfter : out.toNat + 64 ≤ a.toNat)
    (houtEnd : out.toNat + 32 < 2 ^ 256) :
    fp2SubScheduledA yst out a b = fp2At yst a := by
  unfold fp2SubScheduledA
  unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubScheduledA
  have hp := fp2SubAfterC0Stores_fp2At_after_out yst out a b a
    haEnd haAfter houtEnd
  change Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubAfterC0Stores
        yst out a b) a =
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At yst a at hp
  rw [hp]

theorem fp2SubScheduledB_eq_after_out (yst : EvmState) (out a b : U256)
    (hbEnd : b.toNat + 96 < 2 ^ 256)
    (hbAfter : out.toNat + 64 ≤ b.toNat)
    (houtEnd : out.toNat + 32 < 2 ^ 256) :
    fp2SubScheduledB yst out a b = fp2At yst b := by
  unfold fp2SubScheduledB
  unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubScheduledB
  have hp := fp2SubAfterC0Stores_fp2At_after_out yst out a b b
    hbEnd hbAfter houtEnd
  change Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubAfterC0Stores
        yst out a b) b =
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At yst b at hp
  rw [hp]

theorem fp2SubFinalState_canonical_at_out_after (yst : EvmState)
    (out b : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst out))
    (hb : Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst b))
    (hbEnd : b.toNat + 96 < 2 ^ 256)
    (hbAfter : out.toNat + 64 ≤ b.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    Challenge.Bls12381.ProofSupport.Fp2.Canonical
      (fp2At (fp2SubFinalState yst out out b) out) := by
  change Challenge.Bls12381.ProofSupport.Fp2.Canonical
    (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubFinalState
        yst out out b) out)
  rw [Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubFinalState_output
    _ _ _ _ houtEnd]
  apply fp2SubResult_canonical
  · rw [fp2SubScheduledA_eq_at_out _ _ _ houtEnd]
    exact ha
  · have hB := fp2SubScheduledB_eq_after_out yst out out b
      hbEnd hbAfter (by bv_omega)
    change Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubScheduledB
        yst out out b =
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At yst b at hB
    rw [hB]
    exact hb

theorem fp2SubFinalState_toLawful_at_out_after (yst : EvmState)
    (out b : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst out))
    (hb : Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst b))
    (hbEnd : b.toNat + 96 < 2 ^ 256)
    (hbAfter : out.toNat + 64 ≤ b.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    Challenge.Bls12381.ProofSupport.Fp2.toLawful
        (fp2At (fp2SubFinalState yst out out b) out) =
      Challenge.Bls12381.ProofSupport.Fp2.toLawful (fp2At yst out) -
        Challenge.Bls12381.ProofSupport.Fp2.toLawful (fp2At yst b) := by
  have hA := fp2SubScheduledA_eq_at_out yst out b houtEnd
  have hB := fp2SubScheduledB_eq_after_out yst out out b hbEnd hbAfter
    (by bv_omega)
  change Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubScheduledB
      yst out out b =
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At yst b at hB
  have hca : Challenge.Bls12381.ProofSupport.Fp2.Canonical
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubScheduledA
        yst out out b) := by
    rw [hA]
    exact ha
  have hcb : Challenge.Bls12381.ProofSupport.Fp2.Canonical
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubScheduledB
        yst out out b) := by
    rw [hB]
    change Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst b)
    exact hb
  change Challenge.Bls12381.ProofSupport.Fp2.toLawful
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
        (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubFinalState
          yst out out b) out) = _
  rw [Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubFinalState_output
      _ _ _ _ houtEnd,
    fp2SubResult_eq_subSource,
    Challenge.Bls12381.ProofSupport.Fp2.toLawful_subSource hca hcb,
    hA, hB]

theorem fp2SubFinalState_canonical_after_before (yst : EvmState)
    (out a b : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst a))
    (hb : Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst b))
    (haEnd : a.toNat + 96 < 2 ^ 256)
    (haAfter : out.toNat + 64 ≤ a.toNat)
    (hbBefore : b.toNat + 128 ≤ out.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    Challenge.Bls12381.ProofSupport.Fp2.Canonical
      (fp2At (fp2SubFinalState yst out a b) out) := by
  change Challenge.Bls12381.ProofSupport.Fp2.Canonical
    (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubFinalState
        yst out a b) out)
  rw [Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubFinalState_output
    _ _ _ _ houtEnd]
  apply fp2SubResult_canonical
  · have hA := fp2SubScheduledA_eq_after_out yst out a b
      haEnd haAfter (by bv_omega)
    change Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubScheduledA
        yst out a b =
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At yst a at hA
    rw [hA]
    exact ha
  · rw [fp2SubScheduledB_eq_before_out yst out a b hbBefore (by bv_omega)]
    exact hb

theorem fp2SubFinalState_toLawful_after_before (yst : EvmState)
    (out a b : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst a))
    (hb : Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst b))
    (haEnd : a.toNat + 96 < 2 ^ 256)
    (haAfter : out.toNat + 64 ≤ a.toNat)
    (hbBefore : b.toNat + 128 ≤ out.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    Challenge.Bls12381.ProofSupport.Fp2.toLawful
        (fp2At (fp2SubFinalState yst out a b) out) =
      Challenge.Bls12381.ProofSupport.Fp2.toLawful (fp2At yst a) -
        Challenge.Bls12381.ProofSupport.Fp2.toLawful (fp2At yst b) := by
  have hA := fp2SubScheduledA_eq_after_out yst out a b
    haEnd haAfter (by bv_omega)
  change Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubScheduledA
      yst out a b =
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At yst a at hA
  have hB := fp2SubScheduledB_eq_before_out yst out a b
    hbBefore (by bv_omega)
  have hca : Challenge.Bls12381.ProofSupport.Fp2.Canonical
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubScheduledA
        yst out a b) := by
    rw [hA]
    exact ha
  have hcb : Challenge.Bls12381.ProofSupport.Fp2.Canonical
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubScheduledB
        yst out a b) := by
    rw [hB]
    exact hb
  change Challenge.Bls12381.ProofSupport.Fp2.toLawful
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
        (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubFinalState
          yst out a b) out) = _
  rw [Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubFinalState_output
      _ _ _ _ houtEnd,
    fp2SubResult_eq_subSource,
    Challenge.Bls12381.ProofSupport.Fp2.toLawful_subSource hca hcb,
    hA, hB]

private theorem fp2MulAfterRealStores_loadWord_after_out
    (yst : EvmState) (out a b : U256) (offset : Nat)
    (hstart : 1664 ≤ offset) (hafter : out.toNat + 64 ≤ offset)
    (hout : out.toNat + 32 < 2 ^ 256) :
    loadWord (fp2MulAfterRealStores yst out a b).memory offset =
      loadWord yst.memory offset := by
  have h32 : (out + BitVec.ofNat 256 32).toNat = out.toNat + 32 := by
    bv_omega
  unfold fp2MulAfterRealStores
  rw [Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterRealStores,
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterRealHigh]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterRealReads yst a b).memory out.toNat _)
      (out + BitVec.ofNat 256 32).toNat _) offset = _
  rw [h32,
    loadWord_storeWord_disjoint _ (out.toNat + 32) offset _
      (by left; omega),
    loadWord_storeWord_disjoint _ out.toNat offset _ (by left; omega)]
  exact fp2MulAfterV1Stores_loadWord_high_input yst a b offset hstart

theorem fp2MulFinalState_fp2At_after_out (yst : EvmState)
    (out a b ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrHigh : 1920 ≤ ptr.toNat)
    (hafter : out.toNat + 128 ≤ ptr.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    fp2At (fp2MulFinalState yst out a b) ptr = fp2At yst ptr := by
  apply fp2At_eq_of_loads
  all_goals
    rw [fp2MulFinalState, fp2MulAfterImagHigh]
    change loadWord
      (storeWord
        (storeWord (fp2MulAfterImagReads yst out a b).memory
          (out + BitVec.ofNat 256 64).toNat _)
        (out + BitVec.ofNat 256 96).toNat _) _ = _
    rw [loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega),
      loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega)]
    have hreads : (fp2MulAfterImagReads yst out a b).memory =
        (fp2MulAfterVSumStores yst out a b).memory := rfl
    rw [hreads, fp2MulAfterVSumStores_loadWord_high _ _ _ _ _
      (by bv_omega)]
    exact fp2MulAfterRealStores_loadWord_after_out yst out a b _
      (by bv_omega) (by bv_omega) (by bv_omega)

private theorem fp2InvAfterRealStores_loadWord_after_out
    (yst : EvmState) (out a : U256) (offset : Nat)
    (hstart : 1728 ≤ offset) (hafter : out.toNat + 64 ≤ offset)
    (hout : out.toNat + 32 < 2 ^ 256) :
    loadWord (fp2InvAfterRealStores yst out a).memory offset =
      loadWord yst.memory offset := by
  unfold fp2InvAfterRealStores
  unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterRealStores
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterRealHigh
  change loadWord
    (storeWord
      (storeWord
        (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterRealCall
          yst a).memory out.toNat _)
      (out + BitVec.ofNat 256 32).toNat _) offset = _
  rw [loadWord_storeWord_disjoint _ _ offset _ (by left; bv_omega),
    loadWord_storeWord_disjoint _ _ offset _ (by left; bv_omega)]
  unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterRealCall
  rw [fpMulFinalState_loadWord_after_scratch (hstart := by omega)]
  rw [Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterRealReads,
    fp2AddReadState_memory]
  exact fp2InvAfterScalarStores_loadWord_high yst a offset hstart

theorem fp2InvFinalState_fp2At_after_out (yst : EvmState)
    (out a ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrHigh : 1728 ≤ ptr.toNat)
    (hafter : out.toNat + 128 ≤ ptr.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    fp2At (fp2InvFinalState yst out a) ptr = fp2At yst ptr := by
  apply fp2At_eq_of_loads
  all_goals
    unfold fp2InvFinalState
    unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvFinalState
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterImagHigh
    change loadWord
      (storeWord
        (storeWord
          (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterImagCall
            yst out a).memory (out + BitVec.ofNat 256 64).toNat _)
        (out + BitVec.ofNat 256 96).toNat _) _ = _
    rw [loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega),
      loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega)]
    unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterImagCall
    rw [fpMulFinalState_loadWord_after_scratch (hstart := by bv_omega)]
    rw [Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterImagReads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterNegReads]
    change loadWord (fp2InvAfterRealStores yst out a).memory _ = _
    exact fp2InvAfterRealStores_loadWord_after_out yst out a _
      (by bv_omega) (by bv_omega) (by bv_omega)

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
