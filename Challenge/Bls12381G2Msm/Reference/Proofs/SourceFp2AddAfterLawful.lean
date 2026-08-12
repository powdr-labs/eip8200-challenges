import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2AfterOutPreservation
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddInputs

set_option warningAsError true

/-! Lawful Fp2 addition with both operands above the fixed output. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport
open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

private theorem fp2AddAfterC0Stores_fp2At_after_out (yst : EvmState)
    (out a b ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hafter : out.toNat + 64 ≤ ptr.toNat)
    (houtEnd : out.toNat + 32 < 2 ^ 256) :
    fp2At (fp2AddAfterC0Stores yst out a b) ptr = fp2At yst ptr := by
  apply fp2At_eq_of_loads
  all_goals
    unfold fp2AddAfterC0Stores
    unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddAfterC0Stores
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddAfterC0High
    change loadWord
      (storeWord
        (storeWord
          (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddAfterC0Reads
            yst a b).memory out.toNat _)
        (out + BitVec.ofNat 256 32).toNat _) _ = _
    rw [loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega),
      loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega)]
    rfl

private theorem fp2AddScheduledA_eq_after_out (yst : EvmState)
    (out a b : U256)
    (haEnd : a.toNat + 96 < 2 ^ 256)
    (haAfter : out.toNat + 64 ≤ a.toNat)
    (houtEnd : out.toNat + 32 < 2 ^ 256) :
    fp2AddScheduledA yst out a b = fp2At yst a := by
  unfold fp2AddScheduledA
  unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddScheduledA
  have hp := fp2AddAfterC0Stores_fp2At_after_out yst out a b a
    haEnd haAfter houtEnd
  change Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddAfterC0Stores
        yst out a b) a =
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At yst a at hp
  rw [hp]

private theorem fp2AddScheduledB_eq_after_out (yst : EvmState)
    (out a b : U256)
    (hbEnd : b.toNat + 96 < 2 ^ 256)
    (hbAfter : out.toNat + 64 ≤ b.toNat)
    (houtEnd : out.toNat + 32 < 2 ^ 256) :
    fp2AddScheduledB yst out a b = fp2At yst b := by
  unfold fp2AddScheduledB
  unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddScheduledB
  have hp := fp2AddAfterC0Stores_fp2At_after_out yst out a b b
    hbEnd hbAfter houtEnd
  change Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddAfterC0Stores
        yst out a b) b =
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At yst b at hp
  rw [hp]

theorem fp2AddFinalState_canonical_after (yst : EvmState)
    (out a b : U256)
    (ha : Fp2.Canonical (fp2At yst a))
    (hb : Fp2.Canonical (fp2At yst b))
    (haEnd : a.toNat + 96 < 2 ^ 256)
    (haAfter : out.toNat + 64 ≤ a.toNat)
    (hbEnd : b.toNat + 96 < 2 ^ 256)
    (hbAfter : out.toNat + 64 ≤ b.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    Fp2.Canonical (fp2At (fp2AddFinalState yst out a b) out) := by
  change Fp2.Canonical
    (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddFinalState
        yst out a b) out)
  rw [fp2AddFinalState_output _ _ _ _ houtEnd]
  apply fp2AddResult_canonical
  · have hA := fp2AddScheduledA_eq_after_out yst out a b
      haEnd haAfter (by bv_omega)
    change Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddScheduledA
        yst out a b = fp2At yst a at hA
    rw [hA]
    exact ha
  · have hB := fp2AddScheduledB_eq_after_out yst out a b
      hbEnd hbAfter (by bv_omega)
    change Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddScheduledB
        yst out a b = fp2At yst b at hB
    rw [hB]
    exact hb

theorem fp2AddFinalState_toLawful_after (yst : EvmState)
    (out a b : U256)
    (ha : Fp2.Canonical (fp2At yst a))
    (hb : Fp2.Canonical (fp2At yst b))
    (haEnd : a.toNat + 96 < 2 ^ 256)
    (haAfter : out.toNat + 64 ≤ a.toNat)
    (hbEnd : b.toNat + 96 < 2 ^ 256)
    (hbAfter : out.toNat + 64 ≤ b.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    Fp2.toLawful (fp2At (fp2AddFinalState yst out a b) out) =
      Fp2.toLawful (fp2At yst a) + Fp2.toLawful (fp2At yst b) := by
  have hA := fp2AddScheduledA_eq_after_out yst out a b
    haEnd haAfter (by bv_omega)
  have hB := fp2AddScheduledB_eq_after_out yst out a b
    hbEnd hbAfter (by bv_omega)
  change Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddScheduledA
      yst out a b =
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At yst a at hA
  change Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddScheduledB
      yst out a b =
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At yst b at hB
  have hca : Fp2.Canonical
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddScheduledA
        yst out a b) := by rw [hA]; exact ha
  have hcb : Fp2.Canonical
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddScheduledB
        yst out a b) := by rw [hB]; exact hb
  change Fp2.toLawful
    (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddFinalState
        yst out a b) out) = _
  rw [fp2AddFinalState_output _ _ _ _ houtEnd, fp2AddResult_eq_addSource,
    Fp2.toLawful_addSource hca hcb, hA, hB]

theorem fp2AddFinalState_canonical_before (yst : EvmState)
    (out a b : U256)
    (ha : Fp2.Canonical (fp2At yst a))
    (hb : Fp2.Canonical (fp2At yst b))
    (haBefore : a.toNat + 128 ≤ out.toNat)
    (hbBefore : b.toNat + 128 ≤ out.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    Fp2.Canonical (fp2At (fp2AddFinalState yst out a b) out) := by
  change Fp2.Canonical
    (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddFinalState
        yst out a b) out)
  rw [fp2AddFinalState_output _ _ _ _ houtEnd]
  apply fp2AddResult_canonical
  · rw [fp2AddScheduledA_eq_before_out _ _ _ _ haBefore (by bv_omega)]
    exact ha
  · rw [fp2AddScheduledB_eq_before_out _ _ _ _ hbBefore (by bv_omega)]
    exact hb

theorem fp2AddFinalState_toLawful_before (yst : EvmState)
    (out a b : U256)
    (ha : Fp2.Canonical (fp2At yst a))
    (hb : Fp2.Canonical (fp2At yst b))
    (haBefore : a.toNat + 128 ≤ out.toNat)
    (hbBefore : b.toNat + 128 ≤ out.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    Fp2.toLawful (fp2At (fp2AddFinalState yst out a b) out) =
      Fp2.toLawful (fp2At yst a) + Fp2.toLawful (fp2At yst b) := by
  have hA := fp2AddScheduledA_eq_before_out yst out a b
    haBefore (by bv_omega)
  have hB := fp2AddScheduledB_eq_before_out yst out a b
    hbBefore (by bv_omega)
  have hca : Fp2.Canonical
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddScheduledA
        yst out a b) := by rw [hA]; exact ha
  have hcb : Fp2.Canonical
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddScheduledB
        yst out a b) := by rw [hB]; exact hb
  change Fp2.toLawful
    (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddFinalState
        yst out a b) out) = _
  rw [fp2AddFinalState_output _ _ _ _ houtEnd, fp2AddResult_eq_addSource,
    Fp2.toLawful_addSource hca hcb, hA, hB]

theorem fp2AddFinalState_canonical_at_out_before (yst : EvmState)
    (out b : U256)
    (ha : Fp2.Canonical (fp2At yst out))
    (hb : Fp2.Canonical (fp2At yst b))
    (hbBefore : b.toNat + 128 ≤ out.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    Fp2.Canonical (fp2At (fp2AddFinalState yst out out b) out) := by
  change Fp2.Canonical
    (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddFinalState
        yst out out b) out)
  rw [fp2AddFinalState_output _ _ _ _ houtEnd]
  apply fp2AddResult_canonical
  · rw [fp2AddScheduledA_eq_at_out _ _ _ houtEnd]
    exact ha
  · rw [fp2AddScheduledB_eq_before_out _ _ _ _ hbBefore (by bv_omega)]
    exact hb

theorem fp2AddFinalState_toLawful_at_out_before (yst : EvmState)
    (out b : U256)
    (ha : Fp2.Canonical (fp2At yst out))
    (hb : Fp2.Canonical (fp2At yst b))
    (hbBefore : b.toNat + 128 ≤ out.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    Fp2.toLawful (fp2At (fp2AddFinalState yst out out b) out) =
      Fp2.toLawful (fp2At yst out) + Fp2.toLawful (fp2At yst b) := by
  have hA := fp2AddScheduledA_eq_at_out yst out b houtEnd
  have hB := fp2AddScheduledB_eq_before_out yst out out b
    hbBefore (by bv_omega)
  have hca : Fp2.Canonical
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddScheduledA
        yst out out b) := by rw [hA]; exact ha
  have hcb : Fp2.Canonical
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddScheduledB
        yst out out b) := by rw [hB]; exact hb
  change Fp2.toLawful
    (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
      (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddFinalState
        yst out out b) out) = _
  rw [fp2AddFinalState_output _ _ _ _ houtEnd, fp2AddResult_eq_addSource,
    Fp2.toLawful_addSource hca hcb, hA, hB]

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
