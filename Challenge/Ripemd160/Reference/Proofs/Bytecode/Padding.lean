import Challenge.EvmProof.Memory
import Challenge.EvmProof.Word
import Batteries.Data.ByteArray
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
/-!
# Byte-level RIPEMD-160 padding model

This is independent of the compiler's control flow.  It describes the exact
message image consumed by compression: `0x80`, zero fill, then the original
bit length as eight little-endian bytes.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.Padding

open EvmSemantics

def messageOffset : Nat := 0x800

/-- `ceil ((n + 9) / 64) * 64`, in the arithmetic form emitted by Yul. -/
def paddedLength (n : Nat) : Nat := ((n + 72) / 64) * 64

def paddedWord (input : ByteArray) : UInt256 :=
  UInt256.shiftLeft
    (UInt256.shiftRight
      (UInt256.ofNat input.size + UInt256.ofNat 72) (UInt256.ofNat 6))
    (UInt256.ofNat 6)

def zeroCount (n : Nat) : Nat := paddedLength n - n - 9

def zeroBytes (n : Nat) : ByteArray :=
  ByteArray.mk (Array.replicate (zeroCount n) 0)

/-- The low 64 bits of `input.size * 8`, least-significant byte first. -/
def lengthBytes (input : ByteArray) : ByteArray :=
  ByteArray.ofFn fun i : Fin 8 =>
    UInt8.ofNat (((input.size * 8) / 2 ^ (8 * i.val)) % 256)

def paddedMessage (input : ByteArray) : ByteArray :=
  input ++ ByteArray.mk #[0x80] ++ zeroBytes input.size ++ lengthBytes input

def copiedMemory (memory input : ByteArray) : ByteArray :=
  MachineState.writeBytes memory input messageOffset

def sentinelMemory (memory input : ByteArray) : ByteArray :=
  MachineState.writeBytes (copiedMemory memory input) (ByteArray.mk #[0x80])
    (messageOffset + input.size)

def paddedMemory (memory input : ByteArray) : ByteArray :=
  MachineState.writeBytes (sentinelMemory memory input) (lengthBytes input)
    (messageOffset + paddedLength input.size - 8)

theorem paddedLength_pos (n : Nat) : 0 < paddedLength n := by
  unfold paddedLength
  have : 0 < (n + 72) / 64 := by omega
  omega

theorem paddedLength_mod (n : Nat) : paddedLength n % 64 = 0 := by
  simp [paddedLength]

theorem input_and_footer_fit (n : Nat) : n + 9 ≤ paddedLength n := by
  unfold paddedLength
  have h := Nat.mod_lt (n + 72) (by omega : 0 < 64)
  have hsplit := Nat.div_add_mod (n + 72) 64
  omega

theorem paddedLength_lt (n : Nat) : paddedLength n < n + 73 := by
  unfold paddedLength
  have h := Nat.mod_lt (n + 72) (by omega : 0 < 64)
  have hsplit := Nat.div_add_mod (n + 72) 64
  omega

theorem paddedWord_eq (input : ByteArray) (hfit : input.size < 2 ^ 64) :
    paddedWord input = UInt256.ofNat (paddedLength input.size) := by
  have hsum : input.size + 72 < 2 ^ 256 := by
    have : 2 ^ 64 + 72 < 2 ^ 256 := by norm_num
    omega
  have hshr : (input.size + 72) >>> 6 < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hsum
  have hmul : ((input.size + 72) >>> 6) * 2 ^ 6 < 2 ^ 256 := by
    rw [Nat.shiftRight_eq_div_pow]
    have hle := Nat.div_mul_le_self (input.size + 72) (2 ^ 6)
    omega
  unfold paddedWord
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat hsum,
    Challenge.EvmProof.Word.shiftRight_ofNat hsum (by omega),
    Challenge.EvmProof.Word.shiftLeft_ofNat hshr (by omega) hmul]
  congr 1
  simp [paddedLength, Nat.shiftRight_eq_div_pow]

theorem zeroCount_add (n : Nat) :
    n + 1 + zeroCount n + 8 = paddedLength n := by
  unfold zeroCount
  have := input_and_footer_fit n
  omega

theorem prefix_size (n : Nat) :
    n + 1 + zeroCount n = paddedLength n - 8 := by
  have hfit := input_and_footer_fit n
  have hadd := zeroCount_add n
  omega

@[simp] theorem zeroBytes_size (n : Nat) :
    (zeroBytes n).size = zeroCount n := by
  simp [zeroBytes, ByteArray.size]

@[simp] theorem lengthBytes_size (input : ByteArray) :
    (lengthBytes input).size = 8 := by
  exact ByteArray.size_ofFn _

@[simp] theorem paddedMessage_size (input : ByteArray) :
    (paddedMessage input).size = paddedLength input.size := by
  simp only [paddedMessage, ByteArray.size_append, zeroBytes_size,
    lengthBytes_size]
  change input.size + 1 + zeroCount input.size + 8 = paddedLength input.size
  exact zeroCount_add input.size

theorem paddedLength_eq_blocks (n : Nat) :
    paddedLength n = (paddedLength n / 64) * 64 := by
  simp [paddedLength]

theorem lengthByte (input : ByteArray) (i : Nat) (hi : i < 8) :
    (lengthBytes input)[i]'(by simpa using hi) =
      UInt8.ofNat (((input.size * 8) / 2 ^ (8 * i)) % 256) := by
  simp only [lengthBytes, ByteArray.getElem_ofFn]

end Challenge.Ripemd160.Reference.Proofs.Bytecode.Padding
