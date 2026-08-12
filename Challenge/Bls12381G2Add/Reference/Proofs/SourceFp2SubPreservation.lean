import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2SubInputs
import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveMulLeft

set_option warningAsError true

/-! # Memory preservation below a frozen G2ADD `fp2Sub` output -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fp2SubFinalState_loadWord_before_out
    (yst : EvmState) (out a b : U256) (offset : Nat)
    (hend : offset + 32 ≤ out.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    loadWord (fp2SubFinalState yst out a b).memory offset =
      loadWord yst.memory offset := by
  unfold fp2SubFinalState fp2SubAfterC1High
  change loadWord
    (storeWord (storeWord (fp2SubAfterC1Reads yst out a b).memory
      (out + BitVec.ofNat 256 64).toNat _)
      (out + BitVec.ofNat 256 96).toNat _) offset = _
  repeat' rw [loadWord_storeWord_disjoint _ _ _ _ (by right; bv_omega)]
  have hreads : (fp2SubAfterC1Reads yst out a b).memory =
      (fp2SubAfterC0Stores yst out a b).memory := rfl
  rw [hreads]
  unfold fp2SubAfterC0Stores fp2SubAfterC0High
  change loadWord (storeWord (storeWord yst.memory out.toNat _)
    (out + BitVec.ofNat 256 32).toNat _) offset = _
  repeat' rw [loadWord_storeWord_disjoint _ _ _ _ (by right; bv_omega)]

theorem fp2SubFinalState_fp2At_before_out
    (yst : EvmState) (out a b ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hbefore : ptr.toNat + 128 ≤ out.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    fp2At (fp2SubFinalState yst out a b) ptr = fp2At yst ptr := by
  apply fp2At_eq_of_loads
  all_goals
    exact fp2SubFinalState_loadWord_before_out yst out a b _
      (by bv_omega) houtEnd

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
