import Challenge.Ripemd160.Reference.Proofs.Bytecode.DirectCorrect

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

/-!
# Aggregate output bridge

This closes the functional postcondition left abstract by `DirectCorrect`.
The reference first clears the 32-byte return window and then writes the five
RIPEMD chaining words little-endian at offsets 12, 16, ..., 28.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.OutputResultBridge

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open DirectCorrect

private def loadedH (s : State) (i : Nat) : State :=
  { s with activeWords := s.activeWordsAfterUInt256 (OutputTrace.hOffset i) 32 }

private def writeLoopState (s : State) (offset : Nat) (word ret : UInt256)
    (tail : List UInt256) : Nat → State
  | 0 => { s with
      pc := UInt256.ofNat 0x3c8
      stack := [⟨0⟩, UInt256.ofNat offset, word, ret] ++ tail }
  | j + 1 => { OutputTrace.writeByte (writeLoopState s offset word ret tail j)
        offset word j with
      pc := UInt256.ofNat 0x3c8
      stack := [UInt256.ofNat (j + 1), UInt256.ofNat offset, word, ret] ++ tail }

private def afterWrittenWord (s : State) (input : ByteArray) (i : Nat) : State :=
  let loaded := loadedH s i
  let written := writeLoopState loaded (12 + 4 * i) (OutputTrace.hWord s i)
    (UInt256.ofNat 0x676) [UInt256.ofNat i, Padding.paddedWord input] 4
  { written with
    pc := UInt256.ofNat 0x654
    stack := [UInt256.ofNat (i + 1), Padding.paddedWord input] }

private def outputLoopState (s : State) (input : ByteArray) : Nat → State
  | 0 => { OutputTrace.zeroOutput s with
      pc := UInt256.ofNat 0x654
      stack := [⟨0⟩, Padding.paddedWord input] }
  | i + 1 => afterWrittenWord (outputLoopState s input i) input i

private def wordBytes (word : UInt256) : ByteArray :=
  ByteArray.mk #[OutputTrace.wordByte word 0, OutputTrace.wordByte word 1,
    OutputTrace.wordByte word 2, OutputTrace.wordByte word 3]

@[simp] private theorem wordBytes_size (word : UInt256) :
    (wordBytes word).size = 4 := by rfl

private theorem writeLoopState_memory_four (s : State) (offset : Nat)
    (word ret : UInt256) (tail : List UInt256) :
    (writeLoopState s offset word ret tail 4).memory =
      MachineState.writeBytes s.memory (wordBytes word) offset := by
  simp only [writeLoopState, OutputTrace.writeByte, Nat.add_zero]
  rw [show offset + 1 = offset + (ByteArray.mk #[OutputTrace.wordByte word 0]).size
      by rfl]
  rw [Memory.writeBytes_append_adjacent]
  rw [show offset + 2 = offset +
      (ByteArray.mk #[OutputTrace.wordByte word 0] ++
        ByteArray.mk #[OutputTrace.wordByte word 1]).size by rfl]
  rw [Memory.writeBytes_append_adjacent]
  rw [show offset + 3 = offset +
      ((ByteArray.mk #[OutputTrace.wordByte word 0] ++
        ByteArray.mk #[OutputTrace.wordByte word 1]) ++
        ByteArray.mk #[OutputTrace.wordByte word 2]).size by rfl]
  rw [Memory.writeBytes_append_adjacent]
  rfl

private theorem writeLoopState_hWord_four (s : State) (offset : Nat)
    (word ret : UInt256) (tail : List UInt256) (i : Nat)
    (hoff : offset + 4 ≤ OutputTrace.hOffset i) :
    OutputTrace.hWord (writeLoopState s offset word ret tail 4) i =
      OutputTrace.hWord s i := by
  unfold OutputTrace.hWord
  rw [writeLoopState_memory_four]
  apply Memory.readWord_writeBytes_disjoint
  right
  simpa using hoff

private theorem outputLoopState_hWord (s : State) (input : ByteArray)
    (k i : Nat) (hk : k ≤ 5) :
    OutputTrace.hWord (outputLoopState s input k) i = OutputTrace.hWord s i := by
  induction k with
  | zero =>
      unfold outputLoopState OutputTrace.hWord OutputTrace.zeroOutput
      rw [Memory.readWord_writeBytes_disjoint]
      right
      rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
      simp [OutputTrace.hOffset]
  | succ k ih =>
      rw [outputLoopState]
      change OutputTrace.hWord
        (writeLoopState (loadedH (outputLoopState s input k) k)
          (12 + 4 * k) (OutputTrace.hWord (outputLoopState s input k) k)
          (UInt256.ofNat 0x676)
          [UInt256.ofNat k, Padding.paddedWord input] 4) i = _
      rw [writeLoopState_hWord_four]
      · change OutputTrace.hWord (outputLoopState s input k) i = _
        exact ih (by omega)
      · simp [OutputTrace.hOffset]
        omega

private def digestPrefix (s : State) : Nat → ByteArray
  | 0 => ByteArray.empty
  | i + 1 => digestPrefix s i ++ wordBytes (OutputTrace.hWord s i)

@[simp] private theorem digestPrefix_size (s : State) (i : Nat) :
    (digestPrefix s i).size = 4 * i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [digestPrefix, ih]; omega

private theorem outputLoopState_memory (s : State) (input : ByteArray)
    (i : Nat) (hi : i ≤ 5) :
    (outputLoopState s input i).memory =
      MachineState.writeBytes (OutputTrace.zeroOutput s).memory
        (digestPrefix s i) 12 := by
  induction i with
  | zero => simp [outputLoopState, digestPrefix, MachineState.writeBytes]
  | succ i ih =>
      change (writeLoopState (loadedH (outputLoopState s input i) i)
        (12 + 4 * i) (OutputTrace.hWord (outputLoopState s input i) i)
        (UInt256.ofNat 0x676) [UInt256.ofNat i, Padding.paddedWord input] 4).memory = _
      rw [writeLoopState_memory_four]
      change MachineState.writeBytes (outputLoopState s input i).memory
        (wordBytes (OutputTrace.hWord (outputLoopState s input i) i)) (12 + 4 * i) = _
      rw [ih (by omega), outputLoopState_hWord s input i i (by omega)]
      rw [show 12 + 4 * i = 12 + (digestPrefix s i).size by
        rw [digestPrefix_size]]
      rw [Memory.writeBytes_append_adjacent]
      rfl

private def outputBytes (s : State) : ByteArray :=
  ByteArray.mk (Array.replicate 12 0) ++ digestPrefix s 5

@[simp] private theorem outputBytes_size (s : State) :
    (outputBytes s).size = 32 := by
  simp only [outputBytes, ByteArray.size_append, wordBytes_size]
  rw [digestPrefix_size]
  rfl

private theorem readOutput_eq (s : State) (input : ByteArray) :
    MachineState.readPadded (outputLoopState s input 5).memory 0 32 =
      outputBytes s := by
  rw [outputLoopState_memory s input 5 (by omega)]
  apply ByteArray.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < 32 := by simpa using hleft
    rw [← Memory.getD0_eq_getElem _ _ hleft,
      ← Memory.getD0_eq_getElem _ _ hright]
    rw [Memory.readPadded_getElem?_getD, if_pos hi, Nat.zero_add]
    rw [MachineState.writeBytes_getElem?_getD]
    have hdigestSize : (digestPrefix s 5).size = 20 := by simp
    rw [hdigestSize]
    unfold outputBytes
    rw [Memory.getElem?_getD_append]
    have hprefixSize : (ByteArray.mk (Array.replicate 12 0)).size = 12 := by rfl
    rw [hprefixSize]
    by_cases hprefix : i < 12
    · rw [if_neg (by omega), if_pos hprefix]
      unfold OutputTrace.zeroOutput
      rw [MachineState.writeBytes_getElem?_getD,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size, if_pos (by omega)]
      have hzero : (Data.Bytes.natToBytesPadded 0 32)[i]?.getD 0 = 0 := by
        rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD
          0 32 i (by omega)]
        simp
      simp only [Nat.sub_zero]
      rw [hzero]
      rw [Memory.getD0_eq_getElem _ i (by
        change i < 12
        exact hprefix)]
      change 0 = (Array.replicate 12 0)[i]
      symm
      apply Array.getElem_replicate
    · rw [if_pos (by omega), if_neg hprefix]

private theorem wordBytes_ofUInt32 (w : UInt32) :
    wordBytes (Word.ofUInt32 w) = Ripemd160.writeLE32 ByteArray.empty w := by
  unfold wordBytes
  rw [Output.wordByte_ofUInt32 w 0 (by omega),
    Output.wordByte_ofUInt32 w 1 (by omega),
    Output.wordByte_ofUInt32 w 2 (by omega),
    Output.wordByte_ofUInt32 w 3 (by omega)]
  unfold Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push,
    Output.ripemdByte]
  congr 1

private theorem writeLE32_append (acc : ByteArray) (w : UInt32) :
    Ripemd160.writeLE32 acc w =
      acc ++ Ripemd160.writeLE32 ByteArray.empty w := by
  unfold Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  cases acc with
  | mk data =>
      congr 1
      apply Array.ext'
      simp [Array.toList_push, List.append_assoc]
      rfl

private theorem outputBytes_eq_emitDigest (s : State) (H : Array UInt32)
    (hmodel : ∀ i : Fin 5,
      OutputTrace.hWord s i = Word.ofUInt32 H[i]!) :
    outputBytes s = ByteArray.mk (Array.replicate 12 0) ++
      SpecBridge.emitDigest H := by
  simp only [outputBytes, digestPrefix]
  unfold SpecBridge.emitDigest
  have h0 : OutputTrace.hWord s 0 = Word.ofUInt32 H[0]! :=
    hmodel ⟨0, by omega⟩
  have h1 : OutputTrace.hWord s 1 = Word.ofUInt32 H[1]! :=
    hmodel ⟨1, by omega⟩
  have h2 : OutputTrace.hWord s 2 = Word.ofUInt32 H[2]! :=
    hmodel ⟨2, by omega⟩
  have h3 : OutputTrace.hWord s 3 = Word.ofUInt32 H[3]! :=
    hmodel ⟨3, by omega⟩
  have h4 : OutputTrace.hWord s 4 = Word.ofUInt32 H[4]! :=
    hmodel ⟨4, by omega⟩
  rw [h0, h1, h2, h3, h4]
  norm_num [List.range, List.range.loop]
  conv_rhs =>
    rw [writeLE32_append]
    rw [writeLE32_append]
    rw [writeLE32_append]
    rw [writeLE32_append]
  rw [wordBytes_ofUInt32, wordBytes_ofUInt32, wordBytes_ofUInt32,
    wordBytes_ofUInt32, wordBytes_ofUInt32]

private theorem spec_eq (input : ByteArray) :
    spec input = ByteArray.mk (Array.replicate 12 0) ++ Ripemd160.hash input := by
  unfold spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide

private theorem outputBytes_eq_spec (input : ByteArray)
    (seam : CompressionSeam input) :
    outputBytes (seam.states (DriverTrace.blockCount input)) = spec input := by
  let H := SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage input) 0
    (DriverTrace.blockCount input)
  rw [outputBytes_eq_emitDigest _ H seam.finalWords]
  rw [spec_eq, ← HashSpecBridge.paddedHash_eq_hash input]
  rfl

/-- `finalWords` is sufficient to discharge the concrete output machine's
functional result obligation. -/
theorem correctWithSchedule_of_compression
    (seam : ∀ (input : ByteArray), CalldataFits input → CompressionSeam input)
    (hcost : ∀ (input : ByteArray) (hfit : CalldataFits input),
      (fullTrace input hfit (seam input hfit)).cost = GasCost.referenceGas input) :
    GasCost.CorrectWithSchedule referenceBytecode GasCost.referenceGasForSize := by
  apply DirectCorrect.correctWithSchedule_of_compression seam hcost
  intro input hfit
  rw [State.toResult_returned _ (by rfl)]
  congr 1
  change MachineState.readPadded
    (outputLoopState ((seam input hfit).states
      (DriverTrace.blockCount input)) input 5).memory
    0 32 = spec input
  rw [readOutput_eq, outputBytes_eq_spec input (seam input hfit)]

/-- Minimal challenge correctness, now conditional only on compression traces
and their exact-cost telescope. -/
theorem correct_of_compression
    (seam : ∀ (input : ByteArray), CalldataFits input → CompressionSeam input)
    (hcost : ∀ (input : ByteArray) (hfit : CalldataFits input),
      (fullTrace input hfit (seam input hfit)).cost = GasCost.referenceGas input) :
    Correct referenceBytecode :=
  GasCost.correct_of_schedule (correctWithSchedule_of_compression seam hcost)

end Challenge.Ripemd160.Reference.Proofs.Bytecode.OutputResultBridge
