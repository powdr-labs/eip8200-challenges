import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Memory
import YulEvmCompiler.StateRel

set_option warningAsError true

/-!
# Reusable fixed-width Yul word serialization facts

These lemmas connect a left-aligned EVM word stored in Yul memory with the
byte-oriented padded encoders used by the EVM semantics.  They are independent
of any particular challenge.
-/

namespace Challenge.YulProof.Word

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM
open YulEvmCompiler

/-- A 32-byte Yul calldata word agrees with the byte-array view used by the
EVM precompile specifications. -/
theorem wordFrom_toNat (input : ByteArray) (offset : Nat) :
    (wordFrom input.toList offset).toNat =
      Precompile.bytesToNatPadded input offset 32 := by
  have hload := (Challenge.EvmProof.Bytes.memMatch_toList input).loadWord offset
  change conv (wordFrom input.toList offset) =
    MachineState.readWord input offset at hload
  have hnat := congrArg UInt256.toNat hload
  simpa [Challenge.EvmProof.Bytes.readWord_toNat] using hnat

/-- Selecting with the all-zero mask retains the first word. -/
theorem select_zero (x y : U256) :
    x ^^^ (((x ^^^ y) &&& ((0 : U256) - 0))) = x := by
  simp

/-- Selecting with the all-one mask retains the second word. -/
theorem select_one (x y : U256) :
    x ^^^ (((x ^^^ y) &&& ((0 : U256) - 1))) = y := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_xor]
  have hmask : (((0 : U256) - 1).toNat) = 2 ^ 256 - 1 := by
    rw [BitVec.toNat_sub]
    change (2 ^ 256 - 1 + 0) % 2 ^ 256 = 2 ^ 256 - 1
    norm_num
  rw [hmask, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (Nat.xor_lt_two_pow x.isLt y.isLt),
    ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem shiftedWord_toNat (value : U256) (width : Nat)
    (hwidth : width ≤ 32) (hvalue : value.toNat < 256 ^ width) :
    (value <<< (((32 : U256) - BitVec.ofNat 256 width) * 8).toNat).toNat =
      value.toNat * 256 ^ (32 - width) := by
  have hwidthWord : (BitVec.ofNat 256 width).toNat = width := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : width < 2 ^ 256)]
  have hle : BitVec.ofNat 256 width ≤ (32 : U256) := by
    rw [BitVec.le_def, hwidthWord]
    exact hwidth
  have hshift :
      (((32 : U256) - BitVec.ofNat 256 width) * 8).toNat =
        (32 - width) * 8 := by
    rw [BitVec.toNat_mul, BitVec.toNat_sub_of_le hle, hwidthWord]
    change ((32 - width) * 8) % 2 ^ 256 = (32 - width) * 8
    rw [Nat.mod_eq_of_lt (by omega)]
  have hfactor : 0 < 256 ^ (32 - width) := pow_pos (by norm_num) _
  have hbound : value.toNat * 256 ^ (32 - width) < 2 ^ 256 := by
    rw [show (2 : Nat) ^ 256 = 256 ^ 32 by norm_num]
    calc
      value.toNat * 256 ^ (32 - width) <
          256 ^ width * 256 ^ (32 - width) :=
        Nat.mul_lt_mul_of_pos_right hvalue hfactor
      _ = 256 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
  rw [BitVec.toNat_shiftLeft, hshift, Nat.shiftLeft_eq]
  rw [show (2 : Nat) ^ ((32 - width) * 8) = 256 ^ (32 - width) by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]
    congr 1
    omega]
  exact Nat.mod_eq_of_lt hbound

theorem shifted_div (n width k : Nat) (hwidth : width ≤ 32) (hk : k < width) :
    n * 256 ^ (32 - width) / 256 ^ (32 - 1 - k) =
      n / 256 ^ (width - 1 - k) := by
  have hexponent : 32 - 1 - k = (32 - width) + (width - 1 - k) := by omega
  rw [hexponent, Nat.pow_add, Nat.mul_comm (256 ^ (32 - width))]
  exact Nat.mul_div_mul_right n (256 ^ (width - 1 - k))
    (pow_pos (by norm_num) _)

theorem outputMemory_readPadded (outputOffset : Nat) (value : U256) (width : Nat)
    (hwidth : width ≤ 32) (hvalue : value.toNat < 256 ^ width) :
    let shifted := value <<<
      (((32 : U256) - BitVec.ofNat 256 width) * 8).toNat
    MachineState.readPadded
        (MachineState.writeBytes ByteArray.empty
          (Data.Bytes.natToBytesPadded shifted.toNat 32) outputOffset)
        outputOffset width =
      Precompile.natToBytes value.toNat width := by
  dsimp only
  apply ByteArray.ext_getElem
  · rw [Challenge.EvmProof.Memory.readPadded_size, Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro k hleft hright
    have hk : k < width := by
      simpa [Precompile.natToBytes,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hright
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hk,
      MachineState.writeBytes_getElem?_getD, if_pos (by
        constructor
        · omega
        · simp [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
          omega)]
    rw [show outputOffset + k - outputOffset = k by omega,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ 32 k
        (by omega),
      Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ width k hk,
      shiftedWord_toNat value width hwidth hvalue,
      shifted_div value.toNat width k hwidth hk]

theorem readBytes_storeWord_output (outputOffset : Nat)
    (memory : Nat → UInt8) (value : U256) (width : Nat)
    (hmemory : memory = fun _ => 0)
    (hwidth : width ≤ 32) (hvalue : value.toNat < 256 ^ width) :
    let shifted := value <<<
      (((32 : U256) - BitVec.ofNat 256 width) * 8).toNat
    readBytes (storeWord memory outputOffset shifted) outputOffset width =
      (Precompile.natToBytes value.toNat width).toList := by
  dsimp only
  subst memory
  let shifted := value <<< (((32 : U256) - BitVec.ofNat 256 width) * 8).toNat
  have hmatch := YulEvmCompiler.MemMatch.init.storeWord outputOffset shifted
  rw [hmatch.readBytes outputOffset width]
  exact congrArg ByteArray.toList
    (outputMemory_readPadded outputOffset value width hwidth hvalue)

end Challenge.YulProof.Word
