import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvCorrect
import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveMulLeft

set_option warningAsError true

/-! # High-memory preservation below frozen G2ADD `fp2Inv` output -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl

theorem fp2InvFinalState_loadWord_before_out_high
    (yst : EvmState) (out a : U256) (offset : Nat)
    (hstart : 1728 ≤ offset) (hend : offset + 32 ≤ out.toNat)
    (hout : out.toNat + 96 < 2 ^ 256) :
    loadWord (fp2InvFinalState yst out a).memory offset =
      loadWord yst.memory offset := by
  rw [fp2InvFinalState, fp2InvAfterImagHigh]
  change loadWord
    (storeWord
      (storeWord (fp2InvAfterImagCall yst out a).memory
        (out + BitVec.ofNat 256 64).toNat _)
      (out + BitVec.ofNat 256 96).toNat _) offset = _
  rw [loadWord_storeWord_disjoint _ _ offset _ (by right; bv_omega),
    loadWord_storeWord_disjoint _ _ offset _ (by right; bv_omega)]
  unfold fp2InvAfterImagCall
  rw [fpMulFinalState_loadWord_after_scratch (hstart := by omega)]
  rw [fp2InvAfterImagReads, fp2InvAfterNegReads]
  simp only [touchMemory_memory]
  rw [
    fp2InvAfterRealStores_loadWord_before_out yst out a offset
      (by omega) hend (by omega),
    fp2InvAfterScalarStores_loadWord_high yst a offset hstart]

theorem fp2InvFinalState_fp2At_before_out_high
    (yst : EvmState) (out a ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrHigh : 1728 ≤ ptr.toNat)
    (hbefore : ptr.toNat + 128 ≤ out.toNat)
    (hout : out.toNat + 96 < 2 ^ 256) :
    fp2At (fp2InvFinalState yst out a) ptr = fp2At yst ptr := by
  apply fp2At_eq_of_loads
  all_goals
    exact fp2InvFinalState_loadWord_before_out_high yst out a _
      (by bv_omega) (by bv_omega) hout

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
