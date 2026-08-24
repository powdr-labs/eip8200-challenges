import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Memory

set_option warningAsError true

/-! # Functional-memory windows for MODEXP -/

namespace Challenge.EvmProof.ModexpMemory

open EvmSemantics

/-- Package a finite window of the Yul interpreter's functional memory as the
byte-array input consumed by native precompiles. -/
def readWindow (memory : Nat → UInt8) (start size : Nat) : ByteArray :=
  ⟨(YulSemantics.EVM.readBytes memory start size).toArray⟩

@[simp] theorem readWindow_size (memory : Nat → UInt8) (start size : Nat) :
    (readWindow memory start size).size = size := by
  change (YulSemantics.EVM.readBytes memory start size).length = size
  simp [YulSemantics.EVM.readBytes]

/-- A functional-memory read splits at the same address as the corresponding
byte list. -/
theorem readBytes_add (memory : Nat → UInt8) (start left right : Nat) :
    YulSemantics.EVM.readBytes memory start (left + right) =
      YulSemantics.EVM.readBytes memory start left ++
        YulSemantics.EVM.readBytes memory (start + left) right := by
  unfold YulSemantics.EVM.readBytes
  rw [List.range_add, List.map_append, List.map_map]
  congr 2
  funext i
  simp only [Function.comp_apply]
  congr 1
  omega

/-- A Yul `MSTORE` outside a read window leaves that window unchanged. -/
theorem readBytes_storeWord_disjoint (memory : Nat → UInt8)
    (readStart readSize writeStart : Nat) (value : YulSemantics.EVM.U256)
    (hdisjoint : readStart + readSize ≤ writeStart ∨
      writeStart + 32 ≤ readStart) :
    YulSemantics.EVM.readBytes
        (YulSemantics.EVM.storeWord memory writeStart value)
        readStart readSize =
      YulSemantics.EVM.readBytes memory readStart readSize := by
  unfold YulSemantics.EVM.readBytes
  apply List.map_congr_left
  intro i hi
  have hi' : i < readSize := by simpa using hi
  simp only [YulSemantics.EVM.storeWord]
  rw [if_neg]
  omega

/-- A Yul `MSTORE8` outside a read window leaves that window unchanged. -/
theorem readBytes_storeByte_disjoint (memory : Nat → UInt8)
    (readStart readSize writeStart : Nat) (value : YulSemantics.EVM.U256)
    (hdisjoint : readStart + readSize ≤ writeStart ∨
      writeStart < readStart) :
    YulSemantics.EVM.readBytes
        (YulSemantics.EVM.storeByte memory writeStart value)
        readStart readSize =
      YulSemantics.EVM.readBytes memory readStart readSize := by
  unfold YulSemantics.EVM.readBytes
  apply List.map_congr_left
  intro i hi
  have hi' : i < readSize := by simpa using hi
  simp only [YulSemantics.EVM.storeByte]
  rw [if_neg]
  omega

/-- Parsing a fitting subwindow of functional memory is the same big-endian
byte fold as reading that subwindow directly. -/
theorem bytesToNatPadded_readWindow (memory : Nat → UInt8)
    (start size offset width : Nat) (hfit : offset + width ≤ size) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded
        (readWindow memory start size) offset width =
      Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes memory (start + offset) width) := by
  unfold EvmSemantics.EVM.Precompile.bytesToNatPadded
  rw [← Challenge.EvmProof.Bytes.bytesNat_toList]
  rw [Challenge.EvmProof.Bytes.readPadded_toList]
  apply congrArg Challenge.EvmProof.Bytes.bytesNat
  unfold YulSemantics.EVM.readBytes
  apply List.map_congr_left
  intro i hi
  have hiWidth : i < width := by simpa using hi
  unfold YulSemantics.EVM.byteFrom readWindow
  rw [YulEvmCompiler.ByteArray.toList_eq_data]
  simp only [List.getD_eq_getElem?_getD]
  unfold YulSemantics.EVM.readBytes
  rw [List.getElem?_map]
  rw [List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  congr 1
  omega

theorem bytesToNatPadded_readWindow32 (memory : Nat → UInt8)
    (start size offset : Nat) (hfit : offset + 32 ≤ size) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded
        (readWindow memory start size) offset 32 =
      Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes memory (start + offset) 32) :=
  bytesToNatPadded_readWindow memory start size offset 32 hfit

theorem bytesToNatPadded_readWindow48 (memory : Nat → UInt8)
    (start size offset : Nat) (hfit : offset + 48 ≤ size) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded
        (readWindow memory start size) offset 48 =
      Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes memory (start + offset) 48) :=
  bytesToNatPadded_readWindow memory start size offset 48 hfit

theorem bytesToNatPadded_readWindow96 (memory : Nat → UInt8)
    (start size offset : Nat) (hfit : offset + 96 ≤ size) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded
        (readWindow memory start size) offset 96 =
      Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes memory (start + offset) 96) :=
  bytesToNatPadded_readWindow memory start size offset 96 hfit

private def storedWordBytes (value : YulSemantics.EVM.U256) : List UInt8 :=
  (List.range 32).map (fun i => YulSemantics.EVM.byteAt value (31 - i))

private def storedWordBytesPrefix (value : YulSemantics.EVM.U256)
    (width : Nat) : List UInt8 :=
  (List.range width).map (fun i => YulSemantics.EVM.byteAt value (31 - i))

private theorem readBytes_storeWord_prefix (memory : Nat → UInt8)
    (start width : Nat) (value : YulSemantics.EVM.U256)
    (hwidth : width ≤ 32) :
    YulSemantics.EVM.readBytes
        (YulSemantics.EVM.storeWord memory start value) start width =
      storedWordBytesPrefix value width := by
  unfold YulSemantics.EVM.readBytes storedWordBytesPrefix
  apply List.map_congr_left
  intro i hi
  have hi' : i < width := by simpa using hi
  simp only [YulSemantics.EVM.storeWord]
  rw [if_pos]
  · congr 1
    omega
  · constructor <;> omega

private theorem readBytes_storeWord (memory : Nat → UInt8) (start : Nat)
    (value : YulSemantics.EVM.U256) :
    YulSemantics.EVM.readBytes
        (YulSemantics.EVM.storeWord memory start value) start 32 =
      storedWordBytes value := by
  simpa [storedWordBytes, storedWordBytesPrefix] using
    readBytes_storeWord_prefix memory start 32 value (by omega)

/-- Reading back a stored zero word yields exactly 32 zero bytes. -/
theorem readBytes_storeWord_zero (memory : Nat → UInt8) (start : Nat) :
    YulSemantics.EVM.readBytes
        (YulSemantics.EVM.storeWord memory start (0#256)) start 32 =
      List.replicate 32 0 := by
  rw [readBytes_storeWord]
  unfold storedWordBytes
  decide

private theorem bytesNat_storedWordBytesPrefix
    (value : YulSemantics.EVM.U256) (width : Nat) (hwidth : width ≤ 32) :
    Challenge.EvmProof.Bytes.bytesNat (storedWordBytesPrefix value width) =
      value.toNat / 256 ^ (32 - width) := by
  have decodePrefix : ∀ n, n ≤ 32 →
      ((List.range n).map
          (fun i => YulSemantics.EVM.byteAt value (31 - i))).foldl
          (fun acc b => acc * 256 + b.toNat) 0 =
        value.toNat / 256 ^ (32 - n) := by
    intro n hn
    induction n with
    | zero =>
      simp
      symm
      apply Nat.div_eq_of_lt
      simpa [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul] using value.isLt
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.foldl_append]
      simp only [List.map_singleton, List.foldl_cons, List.foldl_nil]
      rw [ih (by omega), YulEvmCompiler.byteAt_eq]
      rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]
      have hsub : 31 - n = 32 - (n + 1) := by omega
      rw [hsub]
      have hpow : 256 ^ (32 - n) = 256 ^ (32 - (n + 1)) * 256 := by
        rw [← Nat.pow_succ]
        congr 1
        omega
      rw [hpow, ← Nat.div_div_eq_div_mul]
      have hdiv := Nat.mod_add_div
        (value.toNat / 256 ^ (32 - (n + 1))) 256
      omega
  unfold storedWordBytesPrefix
  unfold Challenge.EvmProof.Bytes.bytesNat Challenge.EvmProof.Bytes.step
  exact decodePrefix width hwidth

private theorem bytesNat_storedWordBytes (value : YulSemantics.EVM.U256) :
    Challenge.EvmProof.Bytes.bytesNat (storedWordBytes value) = value.toNat := by
  simpa [storedWordBytes, storedWordBytesPrefix] using
    bytesNat_storedWordBytesPrefix value 32 (by omega)

/-- Reading a prefix of the exact 32-byte window written by Yul `MSTORE`
recovers the corresponding big-endian prefix of the source word. -/
theorem bytesNat_readBytes_storeWord_prefix (memory : Nat → UInt8)
    (start width : Nat) (value : YulSemantics.EVM.U256)
    (hwidth : width ≤ 32) :
    Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes
          (YulSemantics.EVM.storeWord memory start value) start width) =
      value.toNat / 256 ^ (32 - width) := by
  rw [readBytes_storeWord_prefix memory start width value hwidth]
  exact bytesNat_storedWordBytesPrefix value width hwidth

/-- Reading back the byte written by Yul `MSTORE8` recovers the source
word's least-significant byte. -/
theorem bytesNat_readBytes_storeByte (memory : Nat → UInt8) (start : Nat)
    (value : YulSemantics.EVM.U256) :
    Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes
          (YulSemantics.EVM.storeByte memory start value) start 1) =
      (YulSemantics.EVM.byteAt value 0).toNat := by
  simp [YulSemantics.EVM.readBytes, YulSemantics.EVM.storeByte,
    Challenge.EvmProof.Bytes.bytesNat, Challenge.EvmProof.Bytes.step]

/-- Reading back the exact 32-byte window written by Yul `MSTORE` recovers
the source word's unsigned value. -/
theorem bytesNat_readBytes_storeWord (memory : Nat → UInt8) (start : Nat)
    (value : YulSemantics.EVM.U256) :
    Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes
          (YulSemantics.EVM.storeWord memory start value) start 32) =
      value.toNat := by
  rw [readBytes_storeWord]
  exact bytesNat_storedWordBytes value

/-- Storing a calldata word and reading it back reproduces the exact padded
32-byte source window. -/
theorem readBytes_storeWord_wordFrom (memory : Nat → UInt8)
    (destination source : Nat) (input : ByteArray) :
    YulSemantics.EVM.readBytes
        (YulSemantics.EVM.storeWord memory destination
          (YulSemantics.EVM.wordFrom input.toList source))
        destination 32 =
      (EvmSemantics.MachineState.readPadded input source 32).toList := by
  apply Challenge.EvmProof.Bytes.bytesNat_injective_of_length
  · simp [YulSemantics.EVM.readBytes,
      Challenge.EvmProof.Bytes.readPadded_toList]
  · rw [bytesNat_readBytes_storeWord,
      Challenge.EvmProof.Bytes.bytesNat_toList]
    have hload := YulEvmCompiler.MemMatch.loadWord
      (Challenge.EvmProof.Bytes.memMatch_toList input) source
    have hnat := congrArg EvmSemantics.UInt256.toNat hload
    rw [YulEvmCompiler.conv_toNat,
      Challenge.EvmProof.Bytes.readWord_toNat] at hnat
    exact hnat

end Challenge.EvmProof.ModexpMemory
