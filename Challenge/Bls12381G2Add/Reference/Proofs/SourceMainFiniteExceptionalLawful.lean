import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteExceptional
import Challenge.Bls12381.ProofSupport.CodecG2
import Challenge.Bls12381.ProofSupport.G2Affine

set_option warningAsError true

/-! # Exact and lawful G2ADD exceptional finite outputs -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

/-- Clearing the eight output words produces the canonical 256-byte infinity
encoding, independently of the input memory. -/
theorem clearPointState_readBytes_zero (yst : EvmState) :
    readBytes (clearPointState yst).memory 0 256 =
      List.replicate 256 0 := by
  change readBytes
    (storeWord
      (storeWord
        (storeWord
          (storeWord
            (storeWord
              (storeWord
                (storeWord
                  (storeWord yst.memory 0 (0#256))
                  32 (0#256))
                64 (0#256))
              96 (0#256))
            128 (0#256))
          160 (0#256))
        192 (0#256))
      224 (0#256)) 0 256 = List.replicate 256 0
  rw [Challenge.EvmProof.ModexpMemory.readBytes_add _ 0 32 224]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 224 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 192 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 160 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 128 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 96 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 64 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 32 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_zero]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_add _ 32 32 192]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 32 32 224 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 32 32 192 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 32 32 160 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 32 32 128 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 32 32 96 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 32 32 64 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_zero]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_add _ 64 32 160]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 64 32 224 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 64 32 192 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 64 32 160 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 64 32 128 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 64 32 96 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_zero]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_add _ 96 32 128]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 96 32 224 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 96 32 192 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 96 32 160 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 96 32 128 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_zero]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_add _ 128 32 96]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 128 32 224 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 128 32 192 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 128 32 160 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_zero]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_add _ 160 32 64]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 160 32 224 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 160 32 192 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_zero]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_add _ 192 32 32]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 192 32 224 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_zero]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_zero]
  repeat' rw [← List.replicate_add]

private theorem natToBytesPadded_zero (width : Nat) :
    EvmSemantics.Data.Bytes.natToBytesPadded 0 width =
      ByteArray.mk (Array.replicate width 0) := by
  apply ByteArray.ext_getElem
  · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    exact Array.size_replicate.symm
  · intro i hiLeft hiRight
    have hi : i < width := by
      rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] at hiLeft
      exact hiLeft
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hiLeft]
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD
      _ _ _ hi]
    norm_num
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hiRight]
    change 0 = (Array.replicate width 0)[i]?.getD 0
    rw [Array.getElem?_eq_getElem (by simpa using hi)]
    simp

/-- The local canonical G2 infinity encoding is exactly 256 zero bytes. -/
theorem encodeG2_infinity_toList :
    (Codec.encodeG2
      (.infinity : EvmSemantics.Crypto.Bls12381.G2Point)).toList =
      List.replicate 256 0 := by
  unfold Codec.encodeG2 EvmSemantics.Crypto.Bls12381G2Add.encodePoint
    EvmSemantics.Crypto.Bls12381Codec.encodeFp2
    EvmSemantics.Crypto.Bls12381Codec.encodeFp
  change ((EvmSemantics.Data.Bytes.natToBytesPadded 0 64 ++
      EvmSemantics.Data.Bytes.natToBytesPadded 0 64) ++
    (EvmSemantics.Data.Bytes.natToBytesPadded 0 64 ++
      EvmSemantics.Data.Bytes.natToBytesPadded 0 64)).toList = _
  repeat' rw [natToBytesPadded_zero]
  simp [YulEvmCompiler.ByteArray.toList_eq_data, ByteArray.data_append]

theorem mainFiniteClear_returned_codec (yst : EvmState) :
    (mainFiniteClearReturnState yst).halted =
      some (HaltKind.ret,
        (Codec.encodeG2
          (.infinity : EvmSemantics.Crypto.Bls12381.G2Point)).toList) := by
  change some (HaltKind.ret,
    readBytes (clearPointState yst).memory 0 256) = _
  rw [clearPointState_readBytes_zero, encodeG2_infinity_toList]

theorem mainFiniteOpposite_affineInfinity
    (x y1 y2 : G2Affine.Field) (hopposite : y1 + y2 = 0) :
    G2Affine.add (.affine x y1) (.affine x y2) = .infinity := by
  simp [G2Affine.add, LawfulAffine.add, hopposite]

theorem mainFiniteZeroY_affineInfinity (x : G2Affine.Field) :
    G2Affine.double (.affine x 0) = .infinity := by
  rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
