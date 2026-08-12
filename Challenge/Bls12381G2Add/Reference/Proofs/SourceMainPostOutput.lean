import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainPostAffine
import Challenge.Bls12381.ProofSupport.CodecG2Core
import Challenge.Bls12381.ProofSupport.CodecRepresentation

set_option warningAsError true

/-! # Exact G2ADD postlude output codec -/

namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private def wordBytes (value : Nat) : List UInt8 :=
  (EvmSemantics.Data.Bytes.natToBytesPadded value 32).toList

private theorem wordBytes_length (value : Nat) :
    (wordBytes value).length = 32 := by
  simpa [wordBytes, YulEvmCompiler.ByteArray.toList_eq_data,
    Array.length_toList] using
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size value 32

private theorem bytesNat_wordBytes (value : Nat) (hvalue : value < 2 ^ 256) :
    Challenge.EvmProof.Bytes.bytesNat (wordBytes value) = value := by
  change EvmSemantics.Data.Bytes.bytesToBigEndianNat
    (EvmSemantics.Data.Bytes.natToBytesPadded value 32) = value
  apply Challenge.EvmProof.Memory.bytesToBigEndianNat_natToBytesPadded
  simpa [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul] using hvalue

private theorem readBytes_storeWord_eq_wordBytes
    (memory : Nat → UInt8) (start : Nat) (word : U256) :
    readBytes (storeWord memory start word) start 32 =
      wordBytes word.toNat := by
  apply Challenge.EvmProof.Bytes.bytesNat_injective_of_length
  · simp [readBytes, wordBytes_length]
  · rw [Challenge.EvmProof.ModexpMemory.bytesNat_readBytes_storeWord,
      bytesNat_wordBytes word.toNat word.isLt]

private theorem wordBytes_pair_eq_encodeFp {a : Fp.Limbs}
    (ha : Fp.Canonical a) :
    wordBytes a.hi.toNat ++ wordBytes a.lo.toNat =
      (Codec.encodeFp (Fp.toField a)).toList := by
  apply Challenge.EvmProof.Bytes.bytesNat_injective_of_length
  · rw [List.length_append, wordBytes_length, wordBytes_length,
      YulEvmCompiler.ByteArray.toList_eq_data, Array.length_toList]
    simp [Codec.fpBytes, Codec.encodeFp_size]
  · rw [Challenge.EvmProof.Bytes.bytesNat_append,
      bytesNat_wordBytes a.hi.toNat a.hi.val.isLt,
      bytesNat_wordBytes a.lo.toNat a.lo.val.isLt, wordBytes_length,
      Challenge.EvmProof.Bytes.bytesNat_toList]
    have hencode := Challenge.EvmProof.Memory.bytesToBigEndianNat_natToBytesPadded
      (Fp.toField a).val 64 (by
        exact (Fp.toField a).isLt.trans (by
          norm_num [EvmSemantics.Crypto.Bls12381.p,
            EvmSemantics.Crypto.Bls12381.absU]))
    rw [show Codec.encodeFp (Fp.toField a) =
      EvmSemantics.Data.Bytes.natToBytesPadded (Fp.toField a).val 64 by rfl,
      hencode]
    rw [show (256 : Nat) ^ 32 = Challenge.EvmProof.Limbs.radix by
      norm_num [Challenge.EvmProof.Limbs.radix, ← pow_mul]]
    rw [show (Fp.toField a).val = Fp.value a by
      simp [Fp.toField, Nat.mod_eq_of_lt ha.2]]
    simp only [Fp.value]
    rw [Nat.mul_comm, Nat.add_comm]

private theorem wordBytes_fp2_eq_encodeFp2 {a : Fp2.Repr}
    (ha : Fp2.Canonical a) :
    wordBytes a.c0.hi.toNat ++ wordBytes a.c0.lo.toNat ++
      wordBytes a.c1.hi.toNat ++ wordBytes a.c1.lo.toNat =
      (Codec.encodeFp2 (Fp2.toField a)).toList := by
  have h0 := wordBytes_pair_eq_encodeFp ha.c0.proof
  have h1 := wordBytes_pair_eq_encodeFp ha.c1.proof
  change _ = (Codec.encodeFp (Fp.toField a.c0) ++
    Codec.encodeFp (Fp.toField a.c1)).toList
  rw [YulEvmCompiler.ByteArray.toList_eq_data] at h0 h1 ⊢
  rw [ByteArray.data_append, Array.toList_append]
  calc
    wordBytes a.c0.hi.toNat ++ wordBytes a.c0.lo.toNat ++
        wordBytes a.c1.hi.toNat ++ wordBytes a.c1.lo.toNat =
      (wordBytes a.c0.hi.toNat ++ wordBytes a.c0.lo.toNat) ++
        (wordBytes a.c1.hi.toNat ++ wordBytes a.c1.lo.toNat) := by
          rw [List.append_assoc]
    _ = _ := congrArg₂ (· ++ ·) h0 h1

private theorem readBytes_eq_wordBytes (memory : Nat → UInt8) (start : Nat) :
    readBytes memory start 32 = wordBytes (loadWord memory start).toNat := by
  have hrestore : readBytes memory start 32 =
      readBytes (storeWord memory start (loadWord memory start)) start 32 := by
    rw [← YulEvmCompiler.Optimizer.ReuseValues.wordBytes_loadWord memory start,
      ← YulEvmCompiler.Optimizer.ReuseValues.wordBytes_loadWord
        (storeWord memory start (loadWord memory start)) start,
      YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord]
  rw [hrestore, readBytes_storeWord_eq_wordBytes]

private theorem readBytes_fp2At_eq_encodeFp2 (st : EvmState) (ptr : U256)
    (hptr : ptr.toNat + 96 < 2 ^ 256)
    (ha : Fp2.Canonical (fp2At st ptr)) :
    readBytes st.memory ptr.toNat 128 =
      (Codec.encodeFp2 (Fp2.toField (fp2At st ptr))).toList := by
  rw [Challenge.EvmProof.ModexpMemory.readBytes_add _ ptr.toNat 32 96,
    Challenge.EvmProof.ModexpMemory.readBytes_add _ (ptr.toNat + 32) 32 64,
    Challenge.EvmProof.ModexpMemory.readBytes_add _ (ptr.toNat + 64) 32 32,
    readBytes_eq_wordBytes, readBytes_eq_wordBytes,
    readBytes_eq_wordBytes, readBytes_eq_wordBytes]
  have h1 : (ptr + BitVec.ofNat 256 32).toNat = ptr.toNat + 32 := by
    bv_omega
  have h2 : (ptr + BitVec.ofNat 256 64).toNat = ptr.toNat + 64 := by
    bv_omega
  have h3 : (ptr + BitVec.ofNat 256 96).toNat = ptr.toNat + 96 := by
    bv_omega
  simpa only [fp2At, YulEvmCompiler.conv_toNat, h1, h2, h3,
    List.append_assoc] using wordBytes_fp2_eq_encodeFp2 ha

/-- A canonical affine point in the first 256 memory bytes is already in the
exact EIP-2537 G2 wire encoding.  Identity branches consume this opaque
boundary instead of expanding eight memory words. -/
theorem readBytes_point_eq_encodeG2 (st : EvmState)
    (hx : Fp2.Canonical (fp2At st 0))
    (hy : Fp2.Canonical (fp2At st 128)) :
    readBytes st.memory 0 256 =
      (Codec.encodeG2 (.affine (Fp2.toField (fp2At st 0))
        (Fp2.toField (fp2At st 128)))).toList := by
  rw [Challenge.EvmProof.ModexpMemory.readBytes_add _ 0 128 128]
  have hxbytes := readBytes_fp2At_eq_encodeFp2 st 0 (by decide) hx
  have hybytes := readBytes_fp2At_eq_encodeFp2 st 128 (by decide) hy
  change readBytes st.memory 0 128 = _ at hxbytes
  change readBytes st.memory 128 128 = _ at hybytes
  rw [hxbytes, hybytes]
  change _ = (Codec.encodeFp2 (Fp2.toField (fp2At st 0)) ++
    Codec.encodeFp2 (Fp2.toField (fp2At st 128))).toList
  conv_rhs => rw [YulEvmCompiler.ByteArray.toList_eq_data]
  rw [ByteArray.data_append, Array.toList_append]
  rw [YulEvmCompiler.ByteArray.toList_eq_data,
    YulEvmCompiler.ByteArray.toList_eq_data]

private theorem mainPostStoredState_readOutput (st : EvmState) :
    readBytes (mainPostStoredState st).memory 0 256 =
      wordBytes (loadWord (mainPostState5 st).memory 2688).toNat ++
      wordBytes (loadWord (mainPostState5 st).memory 2720).toNat ++
      wordBytes (loadWord (mainPostState5 st).memory 2752).toNat ++
      wordBytes (loadWord (mainPostState5 st).memory 2784).toNat ++
      wordBytes (loadWord (mainPostState5 st).memory 2944).toNat ++
      wordBytes (loadWord (mainPostState5 st).memory 2976).toNat ++
      wordBytes (loadWord (mainPostState5 st).memory 3008).toNat ++
      wordBytes (loadWord (mainPostState5 st).memory 3040).toNat := by
  unfold mainPostStoredState
  rw [storePointState_memory_2688_2944]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_add _ 0 32 224]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 224 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 0 32 192 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 0 32 160 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 0 32 128 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 0 32 96 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 0 32 64 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 0 32 32 _ (by omega)]
  rw [readBytes_storeWord_eq_wordBytes]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_add _ 32 32 192]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 32 32 224 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 32 32 192 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 32 32 160 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 32 32 128 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 32 32 96 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 32 32 64 _ (by omega)]
  rw [readBytes_storeWord_eq_wordBytes]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_add _ 64 32 160]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 64 32 224 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 64 32 192 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 64 32 160 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 64 32 128 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 64 32 96 _ (by omega)]
  rw [readBytes_storeWord_eq_wordBytes]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_add _ 96 32 128]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 96 32 224 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 96 32 192 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 96 32 160 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 96 32 128 _ (by omega)]
  rw [readBytes_storeWord_eq_wordBytes]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_add _ 128 32 96]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 128 32 224 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 128 32 192 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 128 32 160 _ (by omega)]
  rw [readBytes_storeWord_eq_wordBytes]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_add _ 160 32 64]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 160 32 224 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 160 32 192 _ (by omega)]
  rw [readBytes_storeWord_eq_wordBytes]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_add _ 192 32 32]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 192 32 224 _ (by omega)]
  rw [readBytes_storeWord_eq_wordBytes, readBytes_storeWord_eq_wordBytes]
  simp only [List.append_assoc]

/-- The exact `storePoint; return(0,256)` tail returns the canonical EIP G2
encoding of the two canonical Fp2 result coordinates. -/
theorem mainPost_returned_codec (st : EvmState)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st 0))
    (hy1 : Fp2.Canonical (fp2At st 128))
    (hx2 : Fp2.Canonical (fp2At st 256)) :
    (mainPostReturnState st).halted =
      some (HaltKind.ret,
        (Codec.encodeG2 (G2Affine.toWire (mainPostPoint st))).toList) := by
  have hcanon := mainPostCoordinates_canonical st hlam hx1 hy1 hx2
  change some (HaltKind.ret,
    readBytes (mainPostStoredState st).memory 0 256) = _
  rw [mainPostStoredState_readOutput]
  simp only [mainPostPoint, G2Affine.toWire, Fp2.toLawful,
    LawfulFp2.toWire_ofWire, Codec.encodeG2,
    EvmSemantics.Crypto.Bls12381G2Add.encodePoint]
  have hxbytes := wordBytes_fp2_eq_encodeFp2 hcanon.1
  have hybytes := wordBytes_fp2_eq_encodeFp2 hcanon.2
  have hx0 : ((2688 : U256).toNat) = 2688 := by decide
  have hx1 : (2688 + BitVec.ofNat 256 32 : U256).toNat = 2720 := by decide
  have hx2 : (2688 + BitVec.ofNat 256 64 : U256).toNat = 2752 := by decide
  have hx3 : (2688 + BitVec.ofNat 256 96 : U256).toNat = 2784 := by decide
  have hy0 : ((2944 : U256).toNat) = 2944 := by decide
  have hy1 : (2944 + BitVec.ofNat 256 32 : U256).toNat = 2976 := by decide
  have hy2 : (2944 + BitVec.ofNat 256 64 : U256).toNat = 3008 := by decide
  have hy3 : (2944 + BitVec.ofNat 256 96 : U256).toNat = 3040 := by decide
  have hxbytes' :
      wordBytes (loadWord (mainPostState5 st).memory 2688).toNat ++
            wordBytes (loadWord (mainPostState5 st).memory 2720).toNat ++
          wordBytes (loadWord (mainPostState5 st).memory 2752).toNat ++
        wordBytes (loadWord (mainPostState5 st).memory 2784).toNat =
      (Codec.encodeFp2 (Fp2.toField
        (fp2At (mainPostState5 st) 2688))).toList := by
    simpa only [fp2At, YulEvmCompiler.conv_toNat, hx0, hx1, hx2, hx3]
      using hxbytes
  have hybytes' :
      wordBytes (loadWord (mainPostState5 st).memory 2944).toNat ++
            wordBytes (loadWord (mainPostState5 st).memory 2976).toNat ++
          wordBytes (loadWord (mainPostState5 st).memory 3008).toNat ++
        wordBytes (loadWord (mainPostState5 st).memory 3040).toNat =
      (Codec.encodeFp2 (Fp2.toField
        (fp2At (mainPostState5 st) 2944))).toList := by
    simpa only [fp2At, YulEvmCompiler.conv_toNat, hy0, hy1, hy2, hy3]
      using hybytes
  congr 2
  calc
    wordBytes (loadWord (mainPostState5 st).memory 2688).toNat ++
              wordBytes (loadWord (mainPostState5 st).memory 2720).toNat ++
            wordBytes (loadWord (mainPostState5 st).memory 2752).toNat ++
          wordBytes (loadWord (mainPostState5 st).memory 2784).toNat ++
        wordBytes (loadWord (mainPostState5 st).memory 2944).toNat ++
      wordBytes (loadWord (mainPostState5 st).memory 2976).toNat ++
    wordBytes (loadWord (mainPostState5 st).memory 3008).toNat ++
      wordBytes (loadWord (mainPostState5 st).memory 3040).toNat =
        (wordBytes (loadWord (mainPostState5 st).memory 2688).toNat ++
              wordBytes (loadWord (mainPostState5 st).memory 2720).toNat ++
            wordBytes (loadWord (mainPostState5 st).memory 2752).toNat ++
          wordBytes (loadWord (mainPostState5 st).memory 2784).toNat) ++
        (wordBytes (loadWord (mainPostState5 st).memory 2944).toNat ++
              wordBytes (loadWord (mainPostState5 st).memory 2976).toNat ++
            wordBytes (loadWord (mainPostState5 st).memory 3008).toNat ++
          wordBytes (loadWord (mainPostState5 st).memory 3040).toNat) := by
            simp only [List.append_assoc]
    _ = _ := by
      simpa only [YulEvmCompiler.ByteArray.toList_eq_data,
        ByteArray.data_append, Array.toList_append] using
          congrArg₂ (· ++ ·) hxbytes' hybytes'

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
