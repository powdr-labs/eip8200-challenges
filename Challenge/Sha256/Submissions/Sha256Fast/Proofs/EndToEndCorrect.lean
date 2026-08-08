import Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailMemoryBridge

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.EndToEndCorrect

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof
open DriverLoop TailState TailMemoryBridge

namespace Ref

abbrev canonicalTail :=
  Challenge.Sha256.Reference.Proofs.Bytecode.HashSpecBridge.canonicalTail
abbrev absorbBlocks :=
  Challenge.Sha256.Reference.Proofs.Bytecode.SpecBridge.absorbBlocks
abbrev absorbBlocks_succ :=
  Challenge.Sha256.Reference.Proofs.Bytecode.SpecBridge.absorbBlocks_succ
abbrev emitDigest :=
  Challenge.Sha256.Reference.Proofs.Bytecode.SpecBridge.emitDigest
abbrev hash_eq_two_phase :=
  Challenge.Sha256.Reference.Proofs.Bytecode.HashSpecBridge.hash_eq_two_phase

end Ref

theorem short_finalHash (s : State) (input : ByteArray) (H : Array UInt32)
    (endW : UInt256) (rest : List UInt256)
    (hfit : CalldataFits input)
    (hcalldata : s.executionEnv.calldata = input)
    (hshort : remainder input < 56) :
    finalHash
        (shortBranch s (endWord input) endW (remWord input)
          (sizeWord input) rest)
        H (endWord input) endW (remWord input) (sizeWord input) rest =
      Ref.absorbBlocks H (Ref.canonicalTail input) 0 1 := by
  change finalHash
      (shortBranch s (endWord input) endW (remWord input)
        (sizeWord input) rest)
      H (endWord input) endW (remWord input) (sizeWord input) rest =
    Sha256.compressBlock H (Ref.canonicalTail input) 0
  unfold finalHash
  apply BlockBridge.compressBlock_eq_window
  · exact canonicalTail_size_short input hshort
  · rw [short_candidate_window s input endW rest hfit hcalldata,
      shortPaddedBlock_eq_canonical input hshort]

theorem long_firstHash (s : State) (input : ByteArray) (H : Array UInt32)
    (endW : UInt256) (rest : List UInt256)
    (hfit : CalldataFits input)
    (hcalldata : s.executionEnv.calldata = input)
    (hlong : ¬ remainder input < 56) :
    firstHash s H (endWord input) endW (remWord input)
        (sizeWord input) rest =
      Sha256.compressBlock H (Ref.canonicalTail input) 0 := by
  unfold firstHash
  calc
    _ = Sha256.compressBlock H
        (MachineState.readPadded (Ref.canonicalTail input) 0 64) 0 := by
      apply BlockBridge.compressBlock_eq_window
      · simp
      · rw [prepared_window s input endW rest hfit hcalldata,
          firstPaddedBlock_eq_canonical_first input hlong]
    _ = _ := (BlockBridge.compressBlock_eq_window H
      (Ref.canonicalTail input)
      (MachineState.readPadded (Ref.canonicalTail input) 0 64) 0
      (by simp) rfl).symm

theorem long_finalHash (s : State) (input : ByteArray) (H : Array UInt32)
    (endW : UInt256) (rest : List UInt256)
    (hfit : CalldataFits input)
    (hlong : ¬ remainder input < 56) :
    finalHash
        (cleared s H (endWord input) endW (remWord input)
          (sizeWord input) rest)
        (firstHash s H (endWord input) endW (remWord input)
          (sizeWord input) rest)
        (endWord input) endW (remWord input) (sizeWord input) rest =
      Sha256.compressBlock
        (firstHash s H (endWord input) endW (remWord input)
          (sizeWord input) rest)
        (Ref.canonicalTail input) 64 := by
  unfold finalHash
  calc
    _ = Sha256.compressBlock
        (firstHash s H (endWord input) endW (remWord input)
          (sizeWord input) rest)
        (MachineState.readPadded (Ref.canonicalTail input) 64 64) 0 := by
      apply BlockBridge.compressBlock_eq_window
      · simp
      · rw [long_last_candidate_window s input H endW rest hfit,
          lastPaddedBlock_eq_canonical_last input hlong]
    _ = _ := (BlockBridge.compressBlock_eq_window
      (firstHash s H (endWord input) endW (remWord input)
        (sizeWord input) rest)
      (Ref.canonicalTail input)
      (MachineState.readPadded (Ref.canonicalTail input) 64 64) 64
      (by simp) rfl).symm

theorem long_finalHash_eq_absorb (s : State) (input : ByteArray)
    (H : Array UInt32) (endW : UInt256) (rest : List UInt256)
    (hfit : CalldataFits input)
    (hcalldata : s.executionEnv.calldata = input)
    (hlong : ¬ remainder input < 56) :
    finalHash
        (cleared s H (endWord input) endW (remWord input)
          (sizeWord input) rest)
        (firstHash s H (endWord input) endW (remWord input)
          (sizeWord input) rest)
        (endWord input) endW (remWord input) (sizeWord input) rest =
      Ref.absorbBlocks H (Ref.canonicalTail input) 0 2 := by
  change finalHash
      (cleared s H (endWord input) endW (remWord input)
        (sizeWord input) rest)
      (firstHash s H (endWord input) endW (remWord input)
        (sizeWord input) rest)
      (endWord input) endW (remWord input) (sizeWord input) rest =
    Sha256.compressBlock
      (Sha256.compressBlock H (Ref.canonicalTail input) 0)
      (Ref.canonicalTail input) 64
  rw [long_finalHash s input H endW rest hfit hlong,
    long_firstHash s input H endW rest hfit hcalldata hlong]

@[simp] theorem finalState_hReturn (input : ByteArray)
    (hfit : CalldataFits input) :
    (EndToEndTrace.finalState input).hReturn = Challenge.Sha256.spec input := by
  let s := EndToEndTrace.tailReady input
  let H := hashAt input (blockCount input)
  by_cases hshort : input.size % 64 < 56
  · have hshort' : remainder input < 56 := by simpa [remainder] using hshort
    rw [EndToEndTrace.finalState, if_pos hshort]
    rw [TailCorrect.shortResult, TailOutput.outputResult_return]
    rw [short_finalHash s input H (endWord input) [] hfit
      (by simp [s]) hshort']
    unfold Challenge.Sha256.spec
    rw [Ref.hash_eq_two_phase input]
    rw [canonicalTail_size_short input hshort']
    simp [H, hashAt, blockCount]
  · have hlong' : ¬ remainder input < 56 := by simpa [remainder] using hshort
    rw [EndToEndTrace.finalState, if_neg hshort]
    rw [TailCorrect.longResult, TailOutput.outputResult_return]
    rw [long_finalHash_eq_absorb s input H (endWord input) [] hfit
      (by simp [s]) hlong']
    unfold Challenge.Sha256.spec
    rw [Ref.hash_eq_two_phase input]
    rw [canonicalTail_size_long input hlong']
    simp [H, hashAt, blockCount]

@[simp] theorem finalState_toResult (input : ByteArray)
    (hfit : CalldataFits input) :
    (EndToEndTrace.finalState input).toResult =
      .returned (Challenge.Sha256.spec input) := by
  rw [State.toResult_returned _ (by
    by_cases hshort : input.size % 64 < 56
    · simp [EndToEndTrace.finalState, hshort, TailCorrect.shortResult]
    · simp [EndToEndTrace.finalState, hshort, TailCorrect.longResult])]
  rw [finalState_hReturn input hfit]

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.EndToEndCorrect
