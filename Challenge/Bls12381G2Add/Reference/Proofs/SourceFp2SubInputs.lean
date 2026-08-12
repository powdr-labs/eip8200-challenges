import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2SubOutput

set_option warningAsError true

/-! # Non-overlapping and in-place inputs for frozen G2ADD `fp2Sub` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

private theorem fp2SubAfterC0Stores_c1_before_out
    (yst : EvmState) (out a b ptr : U256)
    (hptr : ptr.toNat + 128 ≤ out.toNat)
    (hout : out.toNat + 32 < 2 ^ 256) :
    (fp2At (fp2SubAfterC0Stores yst out a b) ptr).c1 =
      (fp2At yst ptr).c1 := by
  unfold fp2At fp2SubAfterC0Stores fp2SubAfterC0High
  change ({
    hi := YulEvmCompiler.conv (loadWord
      (storeWord (storeWord (fp2SubAfterC0Reads yst a b).memory
        out.toNat _) (out + BitVec.ofNat 256 32).toNat _)
      (ptr + BitVec.ofNat 256 64).toNat)
    lo := YulEvmCompiler.conv (loadWord
      (storeWord (storeWord (fp2SubAfterC0Reads yst a b).memory
        out.toNat _) (out + BitVec.ofNat 256 32).toNat _)
      (ptr + BitVec.ofNat 256 96).toNat) } :
      Challenge.Bls12381.ProofSupport.Fp.Limbs) = _
  repeat' rw [loadWord_storeWord_disjoint _ _ _ _ (by right; bv_omega)]
  have hreads : (fp2SubAfterC0Reads yst a b).memory = yst.memory := rfl
  rw [hreads]

private theorem fp2SubAfterC0Stores_c1_at_out
    (yst : EvmState) (out a b : U256)
    (hout : out.toNat + 96 < 2 ^ 256) :
    (fp2At (fp2SubAfterC0Stores yst out a b) out).c1 =
      (fp2At yst out).c1 := by
  have h32 : (out + BitVec.ofNat 256 32).toNat = out.toNat + 32 := by
    bv_omega
  have h64 : (out + BitVec.ofNat 256 64).toNat = out.toNat + 64 := by
    bv_omega
  have h96 : (out + BitVec.ofNat 256 96).toNat = out.toNat + 96 := by
    bv_omega
  unfold fp2At fp2SubAfterC0Stores fp2SubAfterC0High
  change ({
    hi := YulEvmCompiler.conv (loadWord
      (storeWord (storeWord (fp2SubAfterC0Reads yst a b).memory
        out.toNat _) (out + BitVec.ofNat 256 32).toNat _)
      (out + BitVec.ofNat 256 64).toNat)
    lo := YulEvmCompiler.conv (loadWord
      (storeWord (storeWord (fp2SubAfterC0Reads yst a b).memory
        out.toNat _) (out + BitVec.ofNat 256 32).toNat _)
      (out + BitVec.ofNat 256 96).toNat) } :
      Challenge.Bls12381.ProofSupport.Fp.Limbs) = _
  rw [h32, h64, h96]
  repeat' rw [loadWord_storeWord_disjoint _ _ _ _ (by omega)]
  have hreads : (fp2SubAfterC0Reads yst a b).memory = yst.memory := rfl
  rw [hreads]

private theorem fp2Repr_ext {left right :
    Challenge.Bls12381.ProofSupport.Fp2.Repr}
    (h0 : left.c0 = right.c0) (h1 : left.c1 = right.c1) : left = right := by
  cases left
  cases right
  simp only [Challenge.Bls12381.ProofSupport.Fp2.Repr.mk.injEq] at ⊢ h0 h1
  exact ⟨h0, h1⟩

theorem fp2SubScheduledA_eq_before_out (yst : EvmState) (out a b : U256)
    (ha : a.toNat + 128 ≤ out.toNat)
    (hout : out.toNat + 32 < 2 ^ 256) :
    fp2SubScheduledA yst out a b = fp2At yst a := by
  apply fp2Repr_ext
  · rfl
  · exact fp2SubAfterC0Stores_c1_before_out yst out a b a ha hout

theorem fp2SubScheduledB_eq_before_out (yst : EvmState) (out a b : U256)
    (hb : b.toNat + 128 ≤ out.toNat)
    (hout : out.toNat + 32 < 2 ^ 256) :
    fp2SubScheduledB yst out a b = fp2At yst b := by
  apply fp2Repr_ext
  · rfl
  · exact fp2SubAfterC0Stores_c1_before_out yst out a b b hb hout

theorem fp2SubScheduledA_eq_at_out (yst : EvmState) (out b : U256)
    (hout : out.toNat + 96 < 2 ^ 256) :
    fp2SubScheduledA yst out out b = fp2At yst out := by
  apply fp2Repr_ext
  · rfl
  · exact fp2SubAfterC0Stores_c1_at_out yst out out b hout

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
