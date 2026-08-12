import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvReadback

set_option warningAsError true

/-! # Imaginary read-back for frozen G2ADD `fp2Inv` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem fp2InvAfterRealStores_loadWord_before_out
    (yst : EvmState) (out a : U256) (offset : Nat)
    (hoffset : 1328 ≤ offset) (hend : offset + 32 ≤ out.toNat)
    (hout : out.toNat + 32 < 2 ^ 256) :
    loadWord (fp2InvAfterRealStores yst out a).memory offset =
      loadWord (fp2InvAfterScalarStores yst a).memory offset := by
  have h32 : (out + BitVec.ofNat 256 32).toNat = out.toNat + 32 := by
    bv_omega
  rw [fp2InvAfterRealStores, fp2InvAfterRealHigh]
  change loadWord
    (storeWord
      (storeWord (fp2InvAfterRealCall yst a).memory out.toNat
        (fp2InvReal yst a).1)
      (out + BitVec.ofNat 256 32).toNat (fp2InvReal yst a).2) offset = _
  rw [h32,
    loadWord_storeWord_disjoint _ (out.toNat + 32) offset _ (by omega),
    loadWord_storeWord_disjoint _ out.toNat offset _ (by omega)]
  unfold fp2InvAfterRealCall
  rw [fpMulFinalState_loadWord_after_scratch (hstart := hoffset)]
  rw [fp2InvAfterRealReads, fp2AddReadState_memory]

theorem fp2InvAfterRealStores_c1 (yst : EvmState) (out a : U256)
    (haHigh : 1920 ≤ a.toNat) (ha : a.toNat + 96 < 2 ^ 256)
    (hdisjoint : a.toNat + 128 ≤ out.toNat)
    (hout : out.toNat + 32 < 2 ^ 256) :
    fpWords
        (loadWord (fp2InvAfterRealStores yst out a).memory
          (a + BitVec.ofNat 256 64).toNat)
        (loadWord (fp2InvAfterRealStores yst out a).memory
          (a + BitVec.ofNat 256 96).toNat) =
      (fp2At yst a).c1 := by
  have h64 : (a + BitVec.ofNat 256 64).toNat = a.toNat + 64 := by
    bv_omega
  have h96 : (a + BitVec.ofNat 256 96).toNat = a.toNat + 96 := by
    bv_omega
  rw [h64, h96,
    fp2InvAfterRealStores_loadWord_before_out yst out a (a.toNat + 64)
      (by omega) (by omega) hout,
    fp2InvAfterRealStores_loadWord_before_out yst out a (a.toNat + 96)
      (by omega) (by omega) hout,
    fp2InvAfterScalarStores_loadWord_high yst a (a.toNat + 64) (by omega),
    fp2InvAfterScalarStores_loadWord_high yst a (a.toNat + 96) (by omega)]
  change fpWords (loadWord yst.memory (a.toNat + 64))
      (loadWord yst.memory (a.toNat + 96)) =
    fpWords (loadWord yst.memory (a + BitVec.ofNat 256 64).toNat)
      (loadWord yst.memory (a + BitVec.ofNat 256 96).toNat)
  rw [h64, h96]

theorem fp2InvAfterRealStores_scalar (yst : EvmState) (out a : U256)
    (houtHigh : 1728 ≤ out.toNat) (hout : out.toNat + 32 < 2 ^ 256) :
    fpWords (loadWord (fp2InvAfterRealStores yst out a).memory 1664)
        (loadWord (fp2InvAfterRealStores yst out a).memory 1696) =
      fp2InvScalarStored yst a := by
  rw [fp2InvAfterRealStores_loadWord_before_out yst out a 1664
      (by omega) (by omega) hout,
    fp2InvAfterRealStores_loadWord_before_out yst out a 1696
      (by omega) (by omega) hout]
  rfl

theorem fp2InvNeg_eq (yst : EvmState) (out a : U256)
    (haHigh : 1920 ≤ a.toNat) (ha : a.toNat + 96 < 2 ^ 256)
    (hdisjoint : a.toNat + 128 ≤ out.toNat)
    (hout : out.toNat + 32 < 2 ^ 256) :
    pairWords (fp2InvNeg yst out a) =
      Fp.subSource (fpWords 0 0) (fp2At yst a).c1 := by
  rw [fp2InvNeg_eq_subSourceZero,
    fp2InvAfterRealStores_c1 yst out a haHigh ha hdisjoint hout]

theorem fp2InvImagScalar_eq (yst : EvmState) (out a : U256)
    (houtHigh : 1728 ≤ out.toNat) (hout : out.toNat + 32 < 2 ^ 256) :
    fp2InvImagScalar yst out a = fp2InvScalarStored yst a := by
  rw [fp2InvImagScalar]
  change fpWords (loadWord (fp2InvAfterRealStores yst out a).memory 1664)
    (loadWord (fp2InvAfterRealStores yst out a).memory 1696) = _
  exact fp2InvAfterRealStores_scalar yst out a houtHigh hout

theorem fp2InvImag_eq (yst : EvmState) (out a : U256)
    (haCanonical : Fp2.Canonical (fp2At yst a))
    (haHigh : 1920 ≤ a.toNat) (ha : a.toNat + 96 < 2 ^ 256)
    (hdisjoint : a.toNat + 128 ≤ out.toNat)
    (houtHigh : 1728 ≤ out.toNat) (hout : out.toNat + 32 < 2 ^ 256) :
    pairWords (fp2InvImag yst out a) =
      Fp.mulCanonical
        (Fp.subSource (fpWords 0 0) (fp2At yst a).c1)
        (Fp.invCanonical
          (Fp.addSource
            (Fp.mulCanonical (fp2At yst a).c0 (fp2At yst a).c0)
            (Fp.mulCanonical (fp2At yst a).c1 (fp2At yst a).c1))) := by
  have hzero : Fp.Canonical (fpWords 0 0) := by
    change Fp.Canonical (Fp.pack 0)
    exact Fp.canonical_pack (by norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU])
  have hneg : Fp.Canonical (pairWords (fp2InvNeg yst out a)) := by
    rw [fp2InvNeg_eq yst out a haHigh ha hdisjoint hout]
    exact Fp.canonical_subSource hzero haCanonical.c1.proof
  let norm := Fp.addSource
    (Fp.mulCanonical (fp2At yst a).c0 (fp2At yst a).c0)
    (Fp.mulCanonical (fp2At yst a).c1 (fp2At yst a).c1)
  have hnorm : Fp.Canonical norm := Fp.canonical_addSource
    (Fp.canonical_mulCanonical haCanonical.c0.proof haCanonical.c0.proof)
    (Fp.canonical_mulCanonical haCanonical.c1.proof haCanonical.c1.proof)
  have hscalar : Fp.Canonical (fp2InvImagScalar yst out a) := by
    rw [fp2InvImagScalar_eq yst out a houtHigh hout,
      fp2InvScalarStored_eq yst a haCanonical haHigh ha]
    exact Fp.canonical_invCanonical hnorm
  rw [fp2InvImag_eq_mulCanonical yst out a hneg hscalar,
    fp2InvNeg_eq yst out a haHigh ha hdisjoint hout,
    fp2InvImagScalar_eq yst out a houtHigh hout,
    fp2InvScalarStored_eq yst a haCanonical haHigh ha]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
