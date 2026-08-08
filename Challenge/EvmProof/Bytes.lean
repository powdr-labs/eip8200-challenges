import EvmSemantics.Data.Bytes
import Mathlib.Tactic.Ring
import YulEvmCompiler.StateRel
import Challenge.EvmProof.Word
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# Big-endian byte arithmetic

Reusable algebra for the fold shared by CALLDATALOAD, MODEXP, and fixed-width
encoders.  These lemmas deliberately mention only lists of bytes.
-/

namespace Challenge.EvmProof.Bytes

open EvmSemantics

def step (acc : Nat) (byte : UInt8) : Nat :=
  acc * 256 + byte.toNat

def bytesNat (bytes : List UInt8) : Nat :=
  bytes.foldl step 0

theorem bytesNat_toList (bytes : ByteArray) :
    bytesNat bytes.toList = Data.Bytes.bytesToBigEndianNat bytes := rfl

theorem memMatch_toList (bytes : ByteArray) :
    YulEvmCompiler.MemMatch
      (YulSemantics.EVM.byteFrom bytes.toList) bytes := by
  intro i
  rw [YulEvmCompiler.ByteArray.toList_eq_data]
  unfold YulSemantics.EVM.byteFrom
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  by_cases hi : i < bytes.size
  · rw [dif_pos hi, Array.getElem?_eq_getElem (by exact hi)]
    rfl
  · have hnone : bytes.data.size ≤ i := by
      change ¬i < bytes.data.size at hi
      omega
    rw [dif_neg hi, Array.getElem?_eq_none_iff.mpr hnone]
    rfl

theorem readPadded_toList (bytes : ByteArray) (offset width : Nat) :
    (EvmSemantics.MachineState.readPadded bytes offset width).toList =
      (List.range width).map
        (fun i => YulSemantics.EVM.byteFrom bytes.toList (offset + i)) := by
  exact (memMatch_toList bytes).readBytes offset width |>.symm

theorem readPadded_toList_succ (bytes : ByteArray) (offset width : Nat) :
    (EvmSemantics.MachineState.readPadded bytes offset (width + 1)).toList =
      (EvmSemantics.MachineState.readPadded bytes offset width).toList ++
        [YulSemantics.EVM.byteFrom bytes.toList (offset + width)] := by
  rw [readPadded_toList, readPadded_toList, List.range_succ, List.map_append]
  rfl

theorem readPadded_toList_add (bytes : ByteArray)
    (offset left right : Nat) :
    (EvmSemantics.MachineState.readPadded bytes offset (left + right)).toList =
      (EvmSemantics.MachineState.readPadded bytes offset left).toList ++
        (EvmSemantics.MachineState.readPadded bytes (offset + left) right).toList := by
  rw [readPadded_toList, readPadded_toList, readPadded_toList,
    List.range_add, List.map_append, List.map_map]
  congr 2
  funext i
  simp only [Function.comp_apply]
  congr 1
  omega

theorem foldl_step (bytes : List UInt8) (acc : Nat) :
    bytes.foldl step acc =
      acc * 256 ^ bytes.length + bytes.foldl step 0 := by
  induction bytes generalizing acc with
  | nil => simp
  | cons byte bytes ih =>
    rw [List.foldl_cons, ih, List.length_cons, Nat.pow_succ]
    rw [List.foldl_cons]
    simp only [step, Nat.zero_mul, Nat.zero_add]
    rw [ih byte.toNat]
    ring

theorem bytesNat_append (left right : List UInt8) :
    bytesNat (left ++ right) =
      bytesNat left * 256 ^ right.length + bytesNat right := by
  unfold bytesNat
  rw [List.foldl_append]
  exact foldl_step right (left.foldl step 0)

theorem bytesNat_cons (byte : UInt8) (bytes : List UInt8) :
    bytesNat (byte :: bytes) =
      byte.toNat * 256 ^ bytes.length + bytesNat bytes := by
  simpa [bytesNat, step] using bytesNat_append [byte] bytes

theorem bytesNat_snoc (bytes : List UInt8) (byte : UInt8) :
    bytesNat (bytes ++ [byte]) = bytesNat bytes * 256 + byte.toNat := by
  rw [bytesNat_append]
  simp [bytesNat, step]

theorem bytesNat_lt_pow (bytes : List UInt8) :
    bytesNat bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp [bytesNat]
  | cons byte bytes ih =>
    rw [bytesNat_cons, List.length_cons, Nat.pow_succ]
    have hbyte : byte.toNat < 256 := byte.toNat_lt
    have hpow : 0 < 256 ^ bytes.length := Nat.pow_pos (by omega)
    calc
      byte.toNat * 256 ^ bytes.length + bytesNat bytes <
          byte.toNat * 256 ^ bytes.length + 256 ^ bytes.length :=
        Nat.add_lt_add_left ih _
      _ = (byte.toNat + 1) * 256 ^ bytes.length := by ring
      _ ≤ 256 * 256 ^ bytes.length :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 256 ^ bytes.length * 256 := Nat.mul_comm _ _

theorem bytesToNatPadded_succ (bytes : ByteArray) (offset width : Nat) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded bytes offset (width + 1) =
      EvmSemantics.EVM.Precompile.bytesToNatPadded bytes offset width * 256 +
        (YulSemantics.EVM.byteFrom bytes.toList (offset + width)).toNat := by
  unfold EvmSemantics.EVM.Precompile.bytesToNatPadded
  rw [← bytesNat_toList, readPadded_toList_succ, bytesNat_snoc,
    bytesNat_toList]

@[simp] theorem bytesToNatPadded_zero_width (bytes : ByteArray) (offset : Nat) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded bytes offset 0 = 0 := by
  unfold EvmSemantics.EVM.Precompile.bytesToNatPadded
  rw [← bytesNat_toList, readPadded_toList]
  rfl

theorem bytesToNatPadded_add (bytes : ByteArray)
    (offset left right : Nat) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded bytes offset (left + right) =
      EvmSemantics.EVM.Precompile.bytesToNatPadded bytes offset left *
          256 ^ right +
        EvmSemantics.EVM.Precompile.bytesToNatPadded bytes (offset + left) right := by
  unfold EvmSemantics.EVM.Precompile.bytesToNatPadded
  rw [← bytesNat_toList, readPadded_toList_add, bytesNat_append,
    bytesNat_toList, bytesNat_toList]
  congr 2
  have h := congrArg List.length (readPadded_toList bytes (offset + left) right)
  simpa using h

theorem bytesToNatPadded_lt_pow (bytes : ByteArray) (offset width : Nat) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded bytes offset width <
      256 ^ width := by
  unfold EvmSemantics.EVM.Precompile.bytesToNatPadded
  rw [← bytesNat_toList]
  have h := bytesNat_lt_pow
    (EvmSemantics.MachineState.readPadded bytes offset width).toList
  have hlen := congrArg List.length (readPadded_toList bytes offset width)
  have hlen' :
      (EvmSemantics.MachineState.readPadded bytes offset width).toList.length =
        width := by simpa using hlen
  simpa [hlen'] using h

theorem readWord_toNat (bytes : ByteArray) (offset : Nat) :
    (EvmSemantics.MachineState.readWord bytes offset).toNat =
      EvmSemantics.EVM.Precompile.bytesToNatPadded bytes offset 32 := by
  unfold EvmSemantics.MachineState.readWord
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have h := bytesToNatPadded_lt_pow bytes offset 32
  change EvmSemantics.Data.Bytes.bytesToBigEndianNat
      (EvmSemantics.MachineState.readPadded bytes offset 32) < 2 ^ 256
  exact h.trans_le (by norm_num)

theorem readWord_shift_toNat (bytes : ByteArray) (offset width : Nat)
    (hwidth : width ≤ 32) :
    (EvmSemantics.MachineState.readWord bytes offset).toNat >>>
        ((32 - width) * 8) =
      EvmSemantics.EVM.Precompile.bytesToNatPadded bytes offset width := by
  let tail := 32 - width
  have hsum : width + tail = 32 := by omega
  have hsplit := bytesToNatPadded_add bytes offset width tail
  rw [hsum] at hsplit
  have hden : 256 ^ tail = 2 ^ (tail * 8) := by
    calc
      256 ^ tail = (2 ^ 8) ^ tail := by norm_num
      _ = 2 ^ (8 * tail) := (Nat.pow_mul 2 8 tail).symm
      _ = 2 ^ (tail * 8) := by rw [Nat.mul_comm]
  have htail := bytesToNatPadded_lt_pow bytes (offset + width) tail
  rw [Nat.shiftRight_eq_div_pow, ← hden, readWord_toNat, hsplit]
  calc
    (EvmSemantics.EVM.Precompile.bytesToNatPadded bytes offset width *
          256 ^ tail +
        EvmSemantics.EVM.Precompile.bytesToNatPadded bytes (offset + width) tail) /
        256 ^ tail =
      (EvmSemantics.EVM.Precompile.bytesToNatPadded bytes (offset + width) tail +
          256 ^ tail *
            EvmSemantics.EVM.Precompile.bytesToNatPadded bytes offset width) /
        256 ^ tail := by
      congr 1
      rw [Nat.add_comm, Nat.mul_comm]
    _ = EvmSemantics.EVM.Precompile.bytesToNatPadded bytes (offset + width) tail /
          256 ^ tail +
        EvmSemantics.EVM.Precompile.bytesToNatPadded bytes offset width :=
      Nat.add_mul_div_left _ _ (Nat.pow_pos (by omega))
    _ = EvmSemantics.EVM.Precompile.bytesToNatPadded bytes offset width := by
      rw [Nat.div_eq_of_lt htail, Nat.zero_add]

theorem shiftRight_readWord (bytes : ByteArray) (offset width : Nat)
    (hpositive : 0 < width) (hwidth : width ≤ 32) :
    EvmSemantics.UInt256.shiftRight
        (EvmSemantics.MachineState.readWord bytes offset)
        (EvmSemantics.UInt256.ofNat ((32 - width) * 8)) =
      EvmSemantics.UInt256.ofNat
        (EvmSemantics.EVM.Precompile.bytesToNatPadded bytes offset width) := by
  rw [show EvmSemantics.MachineState.readWord bytes offset =
      EvmSemantics.UInt256.ofNat
        (EvmSemantics.EVM.Precompile.bytesToNatPadded bytes offset 32) by rfl]
  rw [Challenge.EvmProof.Word.shiftRight_ofNat]
  · congr 1
    simpa [readWord_toNat] using readWord_shift_toNat bytes offset width hwidth
  · exact bytesToNatPadded_lt_pow bytes offset 32 |>.trans_le (by norm_num)
  · omega

theorem byteAt_zero_readWord (bytes : ByteArray) (offset : Nat) :
    EvmSemantics.UInt256.byteAt ⟨0⟩
        (EvmSemantics.MachineState.readWord bytes offset) =
      EvmSemantics.UInt256.ofNat
        (YulSemantics.EVM.byteFrom bytes.toList offset).toNat := by
  have hshift := readWord_shift_toNat bytes offset 1 (by omega)
  have hone := bytesToNatPadded_succ bytes offset 0
  have hbyte :
      EvmSemantics.EVM.Precompile.bytesToNatPadded bytes offset 1 =
        (YulSemantics.EVM.byteFrom bytes.toList offset).toNat := by
    simpa using hone
  unfold EvmSemantics.UInt256.byteAt
  rw [show (⟨0⟩ : EvmSemantics.UInt256).toNat = 0 by rfl]
  rw [if_neg (by omega)]
  congr 1
  rw [show 8 * (31 - 0) = (32 - 1) * 8 by norm_num, hshift, hbyte]
  rw [show 0xff = 2 ^ 8 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (YulSemantics.EVM.byteFrom bytes.toList offset).toNat_lt

/-- `BYTE i (CALLDATALOAD offset)` selects calldata byte `offset + i` for
every in-range EVM byte index. This is the reusable bridge needed by compiled
little-endian decoders. -/
theorem byteAt_readWord (bytes : ByteArray) (offset i : Nat) (hi : i < 32) :
    EvmSemantics.UInt256.byteAt (EvmSemantics.UInt256.ofNat i)
        (EvmSemantics.MachineState.readWord bytes offset) =
      EvmSemantics.UInt256.ofNat
        (YulSemantics.EVM.byteFrom bytes.toList (offset + i)).toNat := by
  unfold EvmSemantics.UInt256.byteAt
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans hi (by norm_num))]
  rw [if_neg (by omega)]
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_ofNat
    (YulSemantics.EVM.byteFrom bytes.toList (offset + i)).toNat]
  rw [Nat.mod_eq_of_lt (Nat.lt_trans
    (YulSemantics.EVM.byteFrom bytes.toList (offset + i)).toNat_lt (by norm_num))]
  rw [show 8 * (31 - i) = (32 - (i + 1)) * 8 by omega]
  rw [readWord_shift_toNat bytes offset (i + 1) (by omega)]
  rw [bytesToNatPadded_succ bytes offset i]
  rw [show 0xff = 2 ^ 8 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  simp [Nat.add_mod,
    Nat.mod_eq_of_lt (YulSemantics.EVM.byteFrom bytes.toList (offset + i)).toNat_lt]
  exact Nat.lt_trans
    (YulSemantics.EVM.byteFrom bytes.toList (offset + i)).toNat_lt (by norm_num)

end Challenge.EvmProof.Bytes
