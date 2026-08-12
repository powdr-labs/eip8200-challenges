import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option warningAsError true

/-! # Big-endian exponent scanning for BLS12-381 `_modexp` -/

namespace Challenge.Bls12381.ProofSupport.Fp

/-- Interpret a high-to-low bit list as a natural number. -/
def binaryValue : List Bool → Nat
  | [] => 0
  | bit :: bits => bit.toNat * 2 ^ bits.length + binaryValue bits

/-- Interpret a big-endian byte list as a natural number. -/
def bytesValue : List UInt8 → Nat
  | [] => 0
  | byte :: bytes => byte.toNat * 256 ^ bytes.length + bytesValue bytes

/-- Significant bits of one byte, highest set bit first. -/
def significantByteBits (byte : UInt8) : List Bool :=
  (Nat.bits byte.toNat).reverse

/-- All eight bits of one byte, most significant first. -/
def byteBits (byte : UInt8) : List Bool :=
  List.replicate (8 - (Nat.bits byte.toNat).length) false ++
    significantByteBits byte

/-- Source `topBit` after scanning down from bit seven. -/
def highestSetBit (byte : UInt8) : Nat :=
  (significantByteBits byte).length - 1

/-- Exact leading-zero-byte scan performed before exponentiation. -/
def dropLeadingZeroBytes : List UInt8 → List UInt8
  | [] => []
  | byte :: bytes =>
      if byte.toNat = 0 then dropLeadingZeroBytes bytes else byte :: bytes

/-- Remaining source loop bits after its first nonzero byte's most significant
bit has been consumed by initializing the accumulator to `aM`. -/
def scanExponent (bytes : List UInt8) : Option (UInt8 × List Bool) :=
  match dropLeadingZeroBytes bytes with
  | [] => none
  | first :: rest => some (first,
      (significantByteBits first).tail ++ rest.flatMap byteBits)

/-- All significant exponent bits in source processing order. -/
def exponentBits (bytes : List UInt8) : List Bool :=
  match dropLeadingZeroBytes bytes with
  | [] => []
  | first :: rest => significantByteBits first ++ rest.flatMap byteBits

theorem binaryValue_append (left right : List Bool) :
    binaryValue (left ++ right) =
      binaryValue left * 2 ^ right.length + binaryValue right := by
  induction left with
  | nil => simp [binaryValue]
  | cons bit bits ih =>
      simp only [List.cons_append, binaryValue, List.length_append,
        ih, pow_add]
      ring

theorem binaryValue_reverse_bits (n : Nat) :
    binaryValue (Nat.bits n).reverse = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [binaryValue]
  | bit bit n hnonzero ih =>
      rw [Nat.bits_append_bit n bit hnonzero, List.reverse_cons,
        binaryValue_append, ih]
      cases bit <;> simp [binaryValue, Nat.bit, Nat.mul_comm]

theorem binaryValue_significantByteBits (byte : UInt8) :
    binaryValue (significantByteBits byte) = byte.toNat := by
  exact binaryValue_reverse_bits byte.toNat

theorem bits_length_le_eight (byte : UInt8) :
    (Nat.bits byte.toNat).length ≤ 8 := by
  rw [Nat.size_eq_bits_len, Nat.size_le]
  have hbyte := byte.toNat_lt
  norm_num at hbyte ⊢
  exact hbyte

theorem length_byteBits (byte : UInt8) : (byteBits byte).length = 8 := by
  unfold byteBits
  rw [List.length_append, List.length_replicate]
  unfold significantByteBits
  rw [List.length_reverse]
  have hlength := bits_length_le_eight byte
  omega

theorem binaryValue_replicate_false (count : Nat) :
    binaryValue (List.replicate count false) = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, binaryValue, ih]
      simp

theorem binaryValue_byteBits (byte : UInt8) :
    binaryValue (byteBits byte) = byte.toNat := by
  unfold byteBits
  rw [binaryValue_append, binaryValue_replicate_false,
    Nat.zero_mul, Nat.zero_add, binaryValue_significantByteBits]

theorem length_flatMap_byteBits (bytes : List UInt8) :
    (bytes.flatMap byteBits).length = 8 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
      simp [length_byteBits, ih, Nat.mul_succ]
      omega

theorem binaryValue_flatMap_byteBits (bytes : List UInt8) :
    binaryValue (bytes.flatMap byteBits) = bytesValue bytes := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
      rw [List.flatMap_cons, binaryValue_append, binaryValue_byteBits,
        length_flatMap_byteBits, ih]
      rw [show 2 ^ (8 * bytes.length) = 256 ^ bytes.length by
        rw [Nat.pow_mul]]
      rfl

theorem bytesValue_dropLeadingZeroBytes (bytes : List UInt8) :
    bytesValue (dropLeadingZeroBytes bytes) = bytesValue bytes := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
      unfold dropLeadingZeroBytes
      by_cases hzero : byte.toNat = 0
      · rw [if_pos hzero, ih]
        simp [bytesValue, hzero]
      · rw [if_neg hzero]

theorem binaryValue_exponentBits (bytes : List UInt8) :
    binaryValue (exponentBits bytes) = bytesValue bytes := by
  rw [← bytesValue_dropLeadingZeroBytes bytes]
  generalize hdrop : dropLeadingZeroBytes bytes = stripped
  cases stripped with
  | nil => simp [exponentBits, hdrop, bytesValue, binaryValue]
  | cons first rest =>
      simp only [exponentBits, hdrop]
      rw [binaryValue_append, binaryValue_significantByteBits,
        length_flatMap_byteBits, binaryValue_flatMap_byteBits]
      rw [show 2 ^ (8 * rest.length) = 256 ^ rest.length by
        rw [Nat.pow_mul]]
      rfl

theorem reverse_bits_eq_true_cons {n : Nat} (hn : n ≠ 0) :
    ∃ rest, (Nat.bits n).reverse = true :: rest := by
  induction n using Nat.binaryRec' with
  | zero => exact (hn rfl).elim
  | bit bit n hbit ih =>
      by_cases hnzero : n = 0
      · subst n
        have htrue : bit = true := by
          cases bit <;> simp_all [Nat.bit]
        subst bit
        exact ⟨[], by simp⟩
      · obtain ⟨rest, hrest⟩ := ih hnzero
        rw [Nat.bits_append_bit n bit hbit, List.reverse_cons, hrest]
        exact ⟨rest ++ [bit], rfl⟩

theorem dropLeadingZeroBytes_head_ne_zero {bytes : List UInt8}
    {first : UInt8} {rest : List UInt8}
    (hdrop : dropLeadingZeroBytes bytes = first :: rest) :
    first.toNat ≠ 0 := by
  induction bytes with
  | nil => simp [dropLeadingZeroBytes] at hdrop
  | cons byte bytes ih =>
      unfold dropLeadingZeroBytes at hdrop
      by_cases hzero : byte.toNat = 0
      · rw [if_pos hzero] at hdrop
        exact ih hdrop
      · rw [if_neg hzero] at hdrop
        cases hdrop
        exact hzero

theorem scanExponent_value {bytes : List UInt8} {first : UInt8}
    {remaining : List Bool}
    (hscan : scanExponent bytes = some (first, remaining)) :
    bytesValue bytes = 2 ^ remaining.length + binaryValue remaining := by
  generalize hdrop : dropLeadingZeroBytes bytes = stripped
  cases stripped with
  | nil => simp [scanExponent, hdrop] at hscan
  | cons head rest =>
      have hnonzero := dropLeadingZeroBytes_head_ne_zero hdrop
      obtain ⟨tail, hbits⟩ := reverse_bits_eq_true_cons hnonzero
      have hsig : significantByteBits head = true :: tail := hbits
      simp only [scanExponent, hdrop, Option.some.injEq, Prod.mk.injEq] at hscan
      rcases hscan with ⟨rfl, rfl⟩
      rw [← binaryValue_exponentBits bytes]
      simp only [exponentBits, hdrop, hsig, List.tail_cons, List.cons_append,
        binaryValue, Bool.toNat_true, Nat.one_mul, List.length_append]

theorem scanExponent_none_value {bytes : List UInt8}
    (hscan : scanExponent bytes = none) : bytesValue bytes = 0 := by
  rw [← bytesValue_dropLeadingZeroBytes bytes]
  generalize hdrop : dropLeadingZeroBytes bytes = stripped
  cases stripped with
  | nil => rfl
  | cons first rest => simp [scanExponent, hdrop] at hscan

end Challenge.Bls12381.ProofSupport.Fp
