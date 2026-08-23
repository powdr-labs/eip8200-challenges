import Challenge.EvmProof.Memory
import Challenge.EvmProof.Bytes
import YulEvmCompiler.BytesLemmas

set_option warningAsError true

/-!
# Fixed byte windows

Generic framing and fixed-width big-endian encoding facts used by EVM
precompile codecs.  This module is independent of any particular precompile.
-/

namespace Challenge.EvmProof.ByteWindow

open EvmSemantics

/-- Extracting the middle byte array from an explicitly framed append returns
that byte array exactly. -/
theorem extract_append_window (pre window suffix : ByteArray) :
    (pre ++ window ++ suffix).extract pre.size
        (pre.size + window.size) = window := by
  apply ByteArray.ext_getElem
  · simp
  · intro i hiLeft hiRight
    rw [ByteArray.getElem_extract]
    rw [ByteArray.getElem_append_left (by
      rw [ByteArray.size_append]
      omega)]
    rw [ByteArray.getElem_append_right (by omega)]
    congr 1
    omega

/-- Big-endian interpretation is local to an explicitly framed byte window.
-/
theorem bytesToBigEndianNat_extract_append (pre window suffix : ByteArray) :
    Data.Bytes.bytesToBigEndianNat
        ((pre ++ window ++ suffix).extract pre.size
          (pre.size + window.size)) =
      Data.Bytes.bytesToBigEndianNat window := by
  rw [extract_append_window]

/-- If `n` fits in `valueWidth` bytes, increasing the fixed width merely adds
zero bytes at the front. -/
theorem natToBytesPadded_prefix_zeros (n prefixWidth valueWidth : Nat)
    (h : n < 256 ^ valueWidth) :
    Data.Bytes.natToBytesPadded n (prefixWidth + valueWidth) =
      ByteArray.mk (Array.replicate prefixWidth 0) ++
        Data.Bytes.natToBytesPadded n valueWidth := by
  apply ByteArray.ext_getElem
  · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
      ByteArray.size_append]
    change prefixWidth + valueWidth =
      (Array.replicate prefixWidth 0).size + _
    rw [Array.size_replicate,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro i hiLeft hiRight
    have hi : i < prefixWidth + valueWidth := by
      simpa [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hiLeft
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hiLeft]
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ i hi]
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hiRight]
    rw [Challenge.EvmProof.Memory.getElem?_getD_append]
    have hzeroSize :
        (ByteArray.mk (Array.replicate prefixWidth 0)).size = prefixWidth := by
      exact Array.size_replicate
    rw [hzeroSize]
    by_cases hiprefix : i < prefixWidth
    · rw [if_pos hiprefix]
      rw [Challenge.EvmProof.Memory.getD0_eq_getElem _ _ (by
        simpa [hzeroSize] using hiprefix)]
      have hiArray : i < (Array.replicate prefixWidth (0 : UInt8)).size := by
        rw [Array.size_replicate]
        exact hiprefix
      change UInt8.ofNat
        (n / 256 ^ (prefixWidth + valueWidth - 1 - i) % 256) =
          (Array.replicate prefixWidth (0 : UInt8))[i]'hiArray
      rw [Array.getElem_replicate]
      have hexponent : valueWidth ≤ prefixWidth + valueWidth - 1 - i := by
        omega
      have hpow : 256 ^ valueWidth ≤
          256 ^ (prefixWidth + valueWidth - 1 - i) :=
        Nat.pow_le_pow_right (by omega) hexponent
      rw [Nat.div_eq_of_lt (h.trans_le hpow)]
      rfl
    · rw [if_neg hiprefix]
      have hiright : i - prefixWidth < valueWidth := by omega
      rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD
        n valueWidth (i - prefixWidth) hiright]
      have hexponent :
          prefixWidth + valueWidth - 1 - i =
            valueWidth - 1 - (i - prefixWidth) := by
        omega
      rw [hexponent]

/-- Fixed-width big-endian encoding is a left inverse of decoding for every
byte array. -/
theorem natToBytesPadded_bytesToBigEndianNat (bytes : ByteArray) :
    Data.Bytes.natToBytesPadded (Data.Bytes.bytesToBigEndianNat bytes)
        bytes.size = bytes := by
  have hvalue :
      Data.Bytes.bytesToBigEndianNat
          (Data.Bytes.natToBytesPadded
            (Data.Bytes.bytesToBigEndianNat bytes) bytes.size) =
        Data.Bytes.bytesToBigEndianNat bytes := by
    apply Challenge.EvmProof.Memory.bytesToBigEndianNat_natToBytesPadded
    rw [← Challenge.EvmProof.Bytes.bytesNat_toList]
    simpa [YulEvmCompiler.ByteArray.toList_eq_data, Array.length_toList] using
      Challenge.EvmProof.Bytes.bytesNat_lt_pow bytes.toList
  have hlength :
      (Data.Bytes.natToBytesPadded
          (Data.Bytes.bytesToBigEndianNat bytes) bytes.size).toList.length =
        bytes.toList.length := by
    simp [YulEvmCompiler.ByteArray.toList_eq_data, Array.length_toList,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  have hlist := Challenge.EvmProof.Bytes.bytesNat_injective_of_length hlength
    (by simpa only [Challenge.EvmProof.Bytes.bytesNat_toList] using hvalue)
  apply ByteArray.ext
  apply Array.ext
  · simpa [YulEvmCompiler.ByteArray.toList_eq_data, Array.length_toList] using
      congrArg List.length hlist
  · intro i hiLeft hiRight
    have hget := congrArg (fun xs : List UInt8 => xs[i]?) hlist
    simpa [YulEvmCompiler.ByteArray.toList_eq_data, Array.getElem?_toList,
      Array.getElem?_eq_getElem hiLeft,
      Array.getElem?_eq_getElem hiRight] using hget

end Challenge.EvmProof.ByteWindow
