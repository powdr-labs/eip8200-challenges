import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2SubRefinement
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpMulMemory

set_option warningAsError true

/-! # Output readback for frozen G2ADD `fp2Sub` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

private theorem fp2SubFinalState_output_c1 (yst : EvmState) (out a b : U256)
    (hout : out.toNat + 96 < 2 ^ 256) :
    (fp2At (fp2SubFinalState yst out a b) out).c1 =
      (fp2SubResult yst out a b).c1 := by
  have h64 : (out + BitVec.ofNat 256 64).toNat = out.toNat + 64 := by
    bv_omega
  have h96 : (out + BitVec.ofNat 256 96).toNat = out.toNat + 96 := by
    bv_omega
  unfold fp2At fp2SubFinalState fp2SubAfterC1High fp2SubResult fpWords
  change ({
    hi := YulEvmCompiler.conv (loadWord
      (storeWord (storeWord (fp2SubAfterC1Reads yst out a b).memory
        (out + BitVec.ofNat 256 64).toNat (fp2SubC1 yst out a b).1)
        (out + BitVec.ofNat 256 96).toNat (fp2SubC1 yst out a b).2)
      (out + BitVec.ofNat 256 64).toNat)
    lo := YulEvmCompiler.conv (loadWord
      (storeWord (storeWord (fp2SubAfterC1Reads yst out a b).memory
        (out + BitVec.ofNat 256 64).toNat (fp2SubC1 yst out a b).1)
        (out + BitVec.ofNat 256 96).toNat (fp2SubC1 yst out a b).2)
      (out + BitVec.ofNat 256 96).toNat) } :
    Challenge.Bls12381.ProofSupport.Fp.Limbs) = _
  rw [h64, h96,
    loadWord_storeWord_disjoint _ (out.toNat + 96) (out.toNat + 64) _
      (by omega),
    loadWord_storeWord_same, loadWord_storeWord_same]

private theorem fp2SubAfterC0Stores_load0 (yst : EvmState) (out a b : U256)
    (hout : out.toNat + 32 < 2 ^ 256) :
    loadWord (fp2SubAfterC0Stores yst out a b).memory out.toNat =
      (fp2SubC0 yst a b).1 := by
  unfold fp2SubAfterC0Stores fp2SubAfterC0High
  change loadWord
    (storeWord (storeWord (fp2SubAfterC0Reads yst a b).memory out.toNat
      (fp2SubC0 yst a b).1) (out + BitVec.ofNat 256 32).toNat
      (fp2SubC0 yst a b).2) out.toNat = _
  have h32 : (out + BitVec.ofNat 256 32).toNat = out.toNat + 32 := by
    bv_omega
  rw [h32,
    loadWord_storeWord_disjoint _ (out.toNat + 32) out.toNat _ (by omega),
    loadWord_storeWord_same]

private theorem fp2SubAfterC0Stores_load32 (yst : EvmState) (out a b : U256) :
    loadWord (fp2SubAfterC0Stores yst out a b).memory
      (out + BitVec.ofNat 256 32).toNat = (fp2SubC0 yst a b).2 := by
  unfold fp2SubAfterC0Stores
  change loadWord (storeWord (fp2SubAfterC0High yst out a b).memory
    (out + BitVec.ofNat 256 32).toNat (fp2SubC0 yst a b).2)
    (out + BitVec.ofNat 256 32).toNat = _
  rw [loadWord_storeWord_same]

private theorem fp2SubFinalState_output_c0 (yst : EvmState) (out a b : U256)
    (hout : out.toNat + 96 < 2 ^ 256) :
    (fp2At (fp2SubFinalState yst out a b) out).c0 =
      (fp2SubResult yst out a b).c0 := by
  have h32 : (out + BitVec.ofNat 256 32).toNat = out.toNat + 32 := by
    bv_omega
  have h64 : (out + BitVec.ofNat 256 64).toNat = out.toNat + 64 := by
    bv_omega
  have h96 : (out + BitVec.ofNat 256 96).toNat = out.toNat + 96 := by
    bv_omega
  unfold fp2At fp2SubFinalState fp2SubAfterC1High fp2SubResult fpWords
  change ({
    hi := YulEvmCompiler.conv (loadWord
      (storeWord (storeWord (fp2SubAfterC1Reads yst out a b).memory
        (out + BitVec.ofNat 256 64).toNat (fp2SubC1 yst out a b).1)
        (out + BitVec.ofNat 256 96).toNat (fp2SubC1 yst out a b).2)
      out.toNat)
    lo := YulEvmCompiler.conv (loadWord
      (storeWord (storeWord (fp2SubAfterC1Reads yst out a b).memory
        (out + BitVec.ofNat 256 64).toNat (fp2SubC1 yst out a b).1)
        (out + BitVec.ofNat 256 96).toNat (fp2SubC1 yst out a b).2)
      (out + BitVec.ofNat 256 32).toNat) } :
    Challenge.Bls12381.ProofSupport.Fp.Limbs) = _
  rw [h32, h64, h96,
    loadWord_storeWord_disjoint _ (out.toNat + 96) out.toNat _ (by omega),
    loadWord_storeWord_disjoint _ (out.toNat + 64) out.toNat _ (by omega),
    loadWord_storeWord_disjoint _ (out.toNat + 96) (out.toNat + 32) _
      (by omega),
    loadWord_storeWord_disjoint _ (out.toNat + 64) (out.toNat + 32) _
      (by omega)]
  have hmem : (fp2SubAfterC1Reads yst out a b).memory =
      (fp2SubAfterC0Stores yst out a b).memory := rfl
  rw [hmem]
  rw [fp2SubAfterC0Stores_load0 yst out a b (by omega)]
  rw [← h32, fp2SubAfterC0Stores_load32]

theorem fp2SubFinalState_output (yst : EvmState) (out a b : U256)
    (hout : out.toNat + 96 < 2 ^ 256) :
    fp2At (fp2SubFinalState yst out a b) out =
      fp2SubResult yst out a b := by
  have h0 := fp2SubFinalState_output_c0 yst out a b hout
  have h1 := fp2SubFinalState_output_c1 yst out a b hout
  generalize hleft : fp2At (fp2SubFinalState yst out a b) out = left at h0 h1 ⊢
  generalize hright : fp2SubResult yst out a b = right at h0 h1 ⊢
  cases left
  cases right
  simp only [Challenge.Bls12381.ProofSupport.Fp2.Repr.mk.injEq] at ⊢ h0 h1
  exact ⟨h0, h1⟩

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
