import Challenge.Sha256.Submissions.Sha256Fast.Proofs.CompressionCorrect
import Challenge.Sha256.Reference.Proofs.Bytecode.HashSpecBridge

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.BlockBridge

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto

namespace HashBridge

abbrev compressBlock_eq_of_readBE32 :=
  Challenge.Sha256.Reference.Proofs.Bytecode.HashSpecBridge.compressBlock_eq_of_readBE32

abbrev readBE32_eq_of_byte :=
  Challenge.Sha256.Reference.Proofs.Bytecode.HashSpecBridge.readBE32_eq_of_byte

end HashBridge

private theorem byteRead_eq_getD (bytes : ByteArray) (i : Nat) :
    (if h : i < bytes.size then bytes[i].toUInt32 else 0) =
      (bytes[i]?.getD 0).toUInt32 := by
  by_cases h : i < bytes.size <;> simp [h]

theorem compressBlock_eq_window (H : Array UInt32) (memory block : ByteArray)
    (off : Nat) (_hsize : block.size = 64)
    (hwindow : MachineState.readPadded memory off 64 = block) :
    Sha256.compressBlock H memory off = Sha256.compressBlock H block 0 := by
  apply HashBridge.compressBlock_eq_of_readBE32
  intro i hi
  apply HashBridge.readBE32_eq_of_byte
  intro j hj
  rw [byteRead_eq_getD, byteRead_eq_getD]
  let q := i * 4 + j
  have hq : q < 64 := by omega
  have hp := Challenge.EvmProof.Memory.readPadded_getElem?_getD
    memory off 64 q
  rw [if_pos hq] at hp
  have heq := congrArg (fun bytes : ByteArray =>
    (bytes[q]?.getD 0).toUInt32) hwindow
  simp only [Nat.zero_add, Nat.add_assoc]
  change (memory[off + q]?.getD 0).toUInt32 =
    (block[q]?.getD 0).toUInt32
  rw [← heq]
  exact congrArg UInt8.toUInt32 hp.symm

theorem compressBlock_staged (H : Array UInt32) (memory block : ByteArray)
    (hsize : block.size = 64) :
    Sha256.compressBlock H
        (MachineState.writeBytes memory block 288) 288 =
      Sha256.compressBlock H block 0 := by
  apply compressBlock_eq_window
  · exact hsize
  · simpa [hsize] using
      Challenge.EvmProof.Memory.readPadded_writeBytes_same memory block 288

theorem readPadded_readPadded (memory : ByteArray)
    (start total off n : Nat) (hinside : off + n ≤ total) :
    MachineState.readPadded (MachineState.readPadded memory start total) off n =
      MachineState.readPadded memory (start + off) n := by
  apply ByteArray.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < n := by simpa using hleft
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      if_pos hi, if_pos (by omega),
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hi]
    congr 2
    omega

theorem compressBlock_stagedCalldata (H : Array UInt32)
    (memory calldata : ByteArray) (off : Nat) :
    Sha256.compressBlock H
        (MachineState.writeBytes memory
          (MachineState.readPadded calldata off 64) 288) 288 =
      Sha256.compressBlock H calldata off := by
  rw [compressBlock_staged H memory (MachineState.readPadded calldata off 64)
    (by simp)]
  symm
  apply compressBlock_eq_window
  · simp
  · rfl

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.BlockBridge
