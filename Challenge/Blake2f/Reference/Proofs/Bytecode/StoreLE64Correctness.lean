import Challenge.Blake2f.ProofSupport.Word
import Challenge.Blake2f.Reference.Proofs.Bytecode.StoreLE64

set_option warningAsError true

/-! Functional certificate for the compiled little-endian writer. -/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.StoreLE64Correctness

open Challenge.Blake2f
open Challenge.Blake2f.ProofSupport
open EvmSemantics

private theorem land_eq (x y : UInt256) : UInt256.land x y = x &&& y := rfl

def wordBytes (value : UInt256) : ByteArray := ByteArray.mk #[
  StoreLE64.wordByte value 0, StoreLE64.wordByte value 1,
  StoreLE64.wordByte value 2, StoreLE64.wordByte value 3,
  StoreLE64.wordByte value 4, StoreLE64.wordByte value 5,
  StoreLE64.wordByte value 6, StoreLE64.wordByte value 7]

@[simp] theorem wordBytes_size (value : UInt256) :
    (wordBytes value).size = 8 := rfl

theorem wordByte_ofUInt64 (value : UInt64) (i : Nat) (hi : i < 8) :
    StoreLE64.wordByte (Word.ofUInt64 value) i =
      ((value >>> UInt64.ofNat (8 * i)) &&& 0xff).toUInt8 := by
  unfold StoreLE64.wordByte
  rw [Word.shiftRight_ofUInt64 value (8 * i) (by omega)]
  have hff : UInt256.ofNat 0xff = Word.ofUInt64 (0xff : UInt64) := by decide
  rw [hff, land_eq, ← Word.ofUInt64_and, Word.ofUInt64_toNat]
  apply UInt8.toNat_inj.mp
  simp [UInt64.toUInt8]
  rw [show 255 = 2 ^ 8 - 1 by norm_num]
  repeat rw [Nat.and_two_pow_sub_one_eq_mod]

theorem writtenMemory_eight (memory : ByteArray) (address : Nat)
    (value : UInt256) :
    StoreLE64.writtenMemory memory address value 8 =
      MachineState.writeBytes memory (wordBytes value) address := by
  simp only [StoreLE64.writtenMemory, StoreLE64.writeByte, Nat.add_zero]
  rw [show address + 1 =
      address + (ByteArray.mk #[StoreLE64.wordByte value 0]).size by rfl,
    Challenge.EvmProof.Memory.writeBytes_append_adjacent]
  rw [show address + 2 = address +
      (ByteArray.mk #[StoreLE64.wordByte value 0] ++
        ByteArray.mk #[StoreLE64.wordByte value 1]).size by rfl,
    Challenge.EvmProof.Memory.writeBytes_append_adjacent]
  rw [show address + 3 = address +
      ((ByteArray.mk #[StoreLE64.wordByte value 0] ++
        ByteArray.mk #[StoreLE64.wordByte value 1]) ++
        ByteArray.mk #[StoreLE64.wordByte value 2]).size by rfl,
    Challenge.EvmProof.Memory.writeBytes_append_adjacent]
  rw [show address + 4 = address +
      (((ByteArray.mk #[StoreLE64.wordByte value 0] ++
        ByteArray.mk #[StoreLE64.wordByte value 1]) ++
        ByteArray.mk #[StoreLE64.wordByte value 2]) ++
        ByteArray.mk #[StoreLE64.wordByte value 3]).size by rfl,
    Challenge.EvmProof.Memory.writeBytes_append_adjacent]
  rw [show address + 5 = address +
      ((((ByteArray.mk #[StoreLE64.wordByte value 0] ++
        ByteArray.mk #[StoreLE64.wordByte value 1]) ++
        ByteArray.mk #[StoreLE64.wordByte value 2]) ++
        ByteArray.mk #[StoreLE64.wordByte value 3]) ++
        ByteArray.mk #[StoreLE64.wordByte value 4]).size by rfl,
    Challenge.EvmProof.Memory.writeBytes_append_adjacent]
  rw [show address + 6 = address +
      (((((ByteArray.mk #[StoreLE64.wordByte value 0] ++
        ByteArray.mk #[StoreLE64.wordByte value 1]) ++
        ByteArray.mk #[StoreLE64.wordByte value 2]) ++
        ByteArray.mk #[StoreLE64.wordByte value 3]) ++
        ByteArray.mk #[StoreLE64.wordByte value 4]) ++
        ByteArray.mk #[StoreLE64.wordByte value 5]).size by rfl,
    Challenge.EvmProof.Memory.writeBytes_append_adjacent]
  rw [show address + 7 = address +
      ((((((ByteArray.mk #[StoreLE64.wordByte value 0] ++
        ByteArray.mk #[StoreLE64.wordByte value 1]) ++
        ByteArray.mk #[StoreLE64.wordByte value 2]) ++
        ByteArray.mk #[StoreLE64.wordByte value 3]) ++
        ByteArray.mk #[StoreLE64.wordByte value 4]) ++
        ByteArray.mk #[StoreLE64.wordByte value 5]) ++
        ByteArray.mk #[StoreLE64.wordByte value 6]).size by rfl,
    Challenge.EvmProof.Memory.writeBytes_append_adjacent]
  rfl

theorem wordBytes_ofUInt64 (value : UInt64) :
    wordBytes (Word.ofUInt64 value) =
      Crypto.Blake2f.writeLE64 ByteArray.empty value := by
  rw [show wordBytes (Word.ofUInt64 value) = ByteArray.mk #[
      StoreLE64.wordByte (Word.ofUInt64 value) 0,
      StoreLE64.wordByte (Word.ofUInt64 value) 1,
      StoreLE64.wordByte (Word.ofUInt64 value) 2,
      StoreLE64.wordByte (Word.ofUInt64 value) 3,
      StoreLE64.wordByte (Word.ofUInt64 value) 4,
      StoreLE64.wordByte (Word.ofUInt64 value) 5,
      StoreLE64.wordByte (Word.ofUInt64 value) 6,
      StoreLE64.wordByte (Word.ofUInt64 value) 7] by rfl]
  rw [wordByte_ofUInt64 value 0 (by omega),
    wordByte_ofUInt64 value 1 (by omega),
    wordByte_ofUInt64 value 2 (by omega),
    wordByte_ofUInt64 value 3 (by omega),
    wordByte_ofUInt64 value 4 (by omega),
    wordByte_ofUInt64 value 5 (by omega),
    wordByte_ofUInt64 value 6 (by omega),
    wordByte_ofUInt64 value 7 (by omega)]
  unfold Crypto.Blake2f.writeLE64
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  congr 1

end Challenge.Blake2f.Reference.Proofs.Bytecode.StoreLE64Correctness
