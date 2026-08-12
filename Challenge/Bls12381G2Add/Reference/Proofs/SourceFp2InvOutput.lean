import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvImagReadback

set_option warningAsError true

/-! # Output memory for frozen G2ADD `fp2Inv` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem fp2InvAfterRealStores_real (yst : EvmState) (out a : U256)
    (hout : out.toNat + 32 < 2 ^ 256) :
    fpWords (loadWord (fp2InvAfterRealStores yst out a).memory out.toNat)
        (loadWord (fp2InvAfterRealStores yst out a).memory
          (out + BitVec.ofNat 256 32).toNat) =
      pairWords (fp2InvReal yst a) := by
  have h32 : (out + BitVec.ofNat 256 32).toNat = out.toNat + 32 := by
    bv_omega
  rw [fp2InvAfterRealStores, fp2InvAfterRealHigh]
  change fpWords
    (loadWord
      (storeWord
        (storeWord (fp2InvAfterRealCall yst a).memory out.toNat
          (fp2InvReal yst a).1)
        (out + BitVec.ofNat 256 32).toNat (fp2InvReal yst a).2) out.toNat)
    (loadWord
      (storeWord
        (storeWord (fp2InvAfterRealCall yst a).memory out.toNat
          (fp2InvReal yst a).1)
        (out + BitVec.ofNat 256 32).toNat (fp2InvReal yst a).2)
      (out + BitVec.ofNat 256 32).toNat) = _
  rw [h32,
    loadWord_storeWord_disjoint _ (out.toNat + 32) out.toNat _ (by omega),
    loadWord_storeWord_same, loadWord_storeWord_same]
  rfl

theorem fp2InvFinalState_c1 (yst : EvmState) (out a : U256)
    (hout : out.toNat + 96 < 2 ^ 256) :
    (fp2At (fp2InvFinalState yst out a) out).c1 =
      pairWords (fp2InvImag yst out a) := by
  have h64 : (out + BitVec.ofNat 256 64).toNat = out.toNat + 64 := by
    bv_omega
  have h96 : (out + BitVec.ofNat 256 96).toNat = out.toNat + 96 := by
    bv_omega
  rw [fp2InvFinalState, fp2InvAfterImagHigh]
  change fpWords
    (loadWord
      (storeWord
        (storeWord (fp2InvAfterImagCall yst out a).memory
          (out + BitVec.ofNat 256 64).toNat (fp2InvImag yst out a).1)
        (out + BitVec.ofNat 256 96).toNat (fp2InvImag yst out a).2)
      (out + BitVec.ofNat 256 64).toNat)
    (loadWord
      (storeWord
        (storeWord (fp2InvAfterImagCall yst out a).memory
          (out + BitVec.ofNat 256 64).toNat (fp2InvImag yst out a).1)
        (out + BitVec.ofNat 256 96).toNat (fp2InvImag yst out a).2)
      (out + BitVec.ofNat 256 96).toNat) = _
  rw [h64, h96,
    loadWord_storeWord_disjoint _ (out.toNat + 96) (out.toNat + 64) _
      (by omega),
    loadWord_storeWord_same, loadWord_storeWord_same]
  rfl

theorem fp2InvFinalState_c0 (yst : EvmState) (out a : U256)
    (houtHigh : 1328 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    (fp2At (fp2InvFinalState yst out a) out).c0 =
      pairWords (fp2InvReal yst a) := by
  have h32 : (out + BitVec.ofNat 256 32).toNat = out.toNat + 32 := by
    bv_omega
  have h64 : (out + BitVec.ofNat 256 64).toNat = out.toNat + 64 := by
    bv_omega
  have h96 : (out + BitVec.ofNat 256 96).toNat = out.toNat + 96 := by
    bv_omega
  rw [fp2InvFinalState, fp2InvAfterImagHigh]
  change fpWords
    (loadWord
      (storeWord
        (storeWord (fp2InvAfterImagCall yst out a).memory
          (out + BitVec.ofNat 256 64).toNat (fp2InvImag yst out a).1)
        (out + BitVec.ofNat 256 96).toNat (fp2InvImag yst out a).2)
      out.toNat)
    (loadWord
      (storeWord
        (storeWord (fp2InvAfterImagCall yst out a).memory
          (out + BitVec.ofNat 256 64).toNat (fp2InvImag yst out a).1)
        (out + BitVec.ofNat 256 96).toNat (fp2InvImag yst out a).2)
      (out + BitVec.ofNat 256 32).toNat) = _
  rw [h32, h64, h96,
    loadWord_storeWord_disjoint _ (out.toNat + 96) out.toNat _ (by omega),
    loadWord_storeWord_disjoint _ (out.toNat + 64) out.toNat _ (by omega),
    loadWord_storeWord_disjoint _ (out.toNat + 96) (out.toNat + 32) _
      (by omega),
    loadWord_storeWord_disjoint _ (out.toNat + 64) (out.toNat + 32) _
      (by omega)]
  unfold fp2InvAfterImagCall
  rw [fpMulFinalState_loadWord_after_scratch (hstart := houtHigh),
    fpMulFinalState_loadWord_after_scratch (hstart := by omega)]
  change fpWords (loadWord (fp2InvAfterRealStores yst out a).memory out.toNat)
    (loadWord (fp2InvAfterRealStores yst out a).memory (out.toNat + 32)) = _
  simpa [h32] using fp2InvAfterRealStores_real yst out a (by omega)

theorem fp2InvFinalState_output (yst : EvmState) (out a : U256)
    (houtHigh : 1328 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    fp2At (fp2InvFinalState yst out a) out =
      Fp2.mkRepr (pairWords (fp2InvReal yst a))
        (pairWords (fp2InvImag yst out a)) := by
  have hc0 := fp2InvFinalState_c0 yst out a houtHigh hout
  have hc1 := fp2InvFinalState_c1 yst out a hout
  cases hresult : fp2At (fp2InvFinalState yst out a) out with
  | mk c0 c1 =>
      simp only [hresult] at hc0 hc1
      rw [hc0, hc1]
      rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
