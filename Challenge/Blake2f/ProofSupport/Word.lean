import Challenge.EvmProof.Word
import EvmSemantics.Crypto.Blake2f
set_option warningAsError true

/-! Reusable 64-bit BLAKE2b words embedded in the EVM's 256-bit word. -/

namespace Challenge.Blake2f.ProofSupport.Word

open EvmSemantics
open Challenge.EvmProof.Word (word_ext word_toNat_ofNat)

def ofUInt64 (x : UInt64) : UInt256 := UInt256.ofNat x.toNat

def toUInt64 (x : UInt256) : UInt64 := UInt64.ofNat x.toNat

def mask64 (x : UInt256) : UInt256 := x &&& UInt256.ofNat 0xffffffffffffffff

@[simp] theorem ofUInt64_toNat (x : UInt64) : (ofUInt64 x).toNat = x.toNat := by
  have hx : x.toNat < 2 ^ 256 := Nat.lt_trans x.toNat_lt (by norm_num)
  rw [ofUInt64, word_toNat_ofNat, Nat.mod_eq_of_lt hx]

@[simp] theorem toUInt64_ofUInt64 (x : UInt64) : toUInt64 (ofUInt64 x) = x := by
  apply UInt64.toNat_inj.mp
  rw [toUInt64, UInt64.toNat_ofNat', ofUInt64_toNat,
    Nat.mod_eq_of_lt x.toNat_lt]

@[simp] theorem toUInt64_toNat (x : UInt256) :
    (toUInt64 x).toNat = x.toNat % 2 ^ 64 := by
  simp [toUInt64]

@[simp] theorem mask64_toNat (x : UInt256) :
    (mask64 x).toNat = x.toNat &&& 0xffffffffffffffff := by
  change (x.val &&& (UInt256.ofNat 0xffffffffffffffff).val).val = _
  rw [Fin.and_val]
  change x.toNat &&& (UInt256.ofNat 0xffffffffffffffff).toNat = _
  rw [word_toNat_ofNat]
  norm_num

theorem mask64_eq_ofUInt64 (x : UInt256) :
    mask64 x = ofUInt64 (toUInt64 x) := by
  apply word_ext
  rw [mask64_toNat, ofUInt64_toNat, toUInt64_toNat]
  rw [show 0xffffffffffffffff = 2 ^ 64 - 1 by norm_num]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

@[simp] theorem mask64_ofUInt64 (x : UInt64) :
    mask64 (ofUInt64 x) = ofUInt64 x := by
  rw [mask64_eq_ofUInt64, toUInt64_ofUInt64]

@[simp] theorem ofUInt64_xor (x y : UInt64) :
    ofUInt64 (x ^^^ y) = ofUInt64 x ^^^ ofUInt64 y := by
  apply word_ext
  rw [ofUInt64_toNat]
  change (x ^^^ y).toNat =
    ((ofUInt64 x).toNat ^^^ (ofUInt64 y).toNat) % UInt256.size
  rw [UInt64.toNat_xor, ofUInt64_toNat, ofUInt64_toNat]
  apply Eq.symm
  apply Nat.mod_eq_of_lt
  exact Nat.lt_trans (Nat.xor_lt_two_pow x.toNat_lt y.toNat_lt) (by
    change 2 ^ 64 < 2 ^ 256
    norm_num)

@[simp] theorem ofUInt64_or (x y : UInt64) :
    ofUInt64 (x ||| y) = ofUInt64 x ||| ofUInt64 y := by
  apply word_ext
  rw [ofUInt64_toNat]
  change (x ||| y).toNat =
    ((ofUInt64 x).toNat ||| (ofUInt64 y).toNat) % UInt256.size
  rw [UInt64.toNat_or, ofUInt64_toNat, ofUInt64_toNat]
  apply Eq.symm
  apply Nat.mod_eq_of_lt
  exact Nat.lt_trans (Nat.or_lt_two_pow x.toNat_lt y.toNat_lt) (by
    change 2 ^ 64 < 2 ^ 256
    norm_num)

@[simp] theorem ofUInt64_and (x y : UInt64) :
    ofUInt64 (x &&& y) = ofUInt64 x &&& ofUInt64 y := by
  apply word_ext
  rw [ofUInt64_toNat]
  change (x &&& y).toNat =
    ((ofUInt64 x).toNat &&& (ofUInt64 y).toNat) % UInt256.size
  rw [UInt64.toNat_and, ofUInt64_toNat, ofUInt64_toNat]
  apply Eq.symm
  apply Nat.mod_eq_of_lt
  exact Nat.lt_trans (Nat.and_lt_two_pow x.toNat y.toNat_lt) (by
    change 2 ^ 64 < 2 ^ 256
    norm_num)

/-- A calldata byte shifted into one of eight little-endian lanes remains a
64-bit value, so EVM `SHL` agrees exactly with `UInt64` shifting. -/
theorem shiftLeft_byte_lane (byte : UInt8) (i : Nat) (hi : i < 8) :
    UInt256.shiftLeft (UInt256.ofNat byte.toNat) (UInt256.ofNat (8 * i)) =
      ofUInt64 (UInt64.ofNat byte.toNat <<< UInt64.ofNat (8 * i)) := by
  have hbyte256 : byte.toNat < 2 ^ 256 := Nat.lt_trans byte.toNat_lt (by norm_num)
  have hshift : 8 * i < 256 := by omega
  have hresult64 : byte.toNat * 2 ^ (8 * i) < 2 ^ 64 := by
    have hb : byte.toNat < 2 ^ 8 := by simpa using byte.toNat_lt
    have hp : 2 ^ (8 * i) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by omega) (by omega)
    calc
      byte.toNat * 2 ^ (8 * i) < 2 ^ 8 * 2 ^ (8 * i) :=
        Nat.mul_lt_mul_of_pos_right hb (Nat.pow_pos (by omega))
      _ ≤ 2 ^ 8 * 2 ^ 56 := Nat.mul_le_mul_left _ hp
      _ = 2 ^ 64 := by norm_num
  have hresult : byte.toNat * 2 ^ (8 * i) < 2 ^ 256 :=
    hresult64.trans (by norm_num)
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat hbyte256 hshift hresult]
  apply word_ext
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hresult, ofUInt64_toNat,
    UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (Nat.lt_trans byte.toNat_lt (by norm_num)),
    Nat.mod_eq_of_lt (by omega : 8 * i < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 8 * i < 64), Nat.shiftLeft_eq]
  change byte.toNat * 2 ^ (8 * i) =
    byte.toNat * 2 ^ (8 * i) % 2 ^ 64
  rw [Nat.mod_eq_of_lt]
  exact hresult64

@[simp] theorem mask64_add (x y : UInt64) :
    mask64 (ofUInt64 x + ofUInt64 y) = ofUInt64 (x + y) := by
  rw [mask64_eq_ofUInt64]
  apply congrArg ofUInt64
  apply UInt64.toNat_inj.mp
  rw [toUInt64_toNat, UInt64.toNat_add]
  change ((ofUInt64 x).val + (ofUInt64 y).val).val % 2 ^ 64 = _
  rw [Fin.val_add]
  change ((ofUInt64 x).toNat + (ofUInt64 y).toNat) % UInt256.size % 2 ^ 64 = _
  rw [ofUInt64_toNat, ofUInt64_toNat,
    show UInt256.size = 2 ^ 256 by rfl,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

/-- Truncating EVM addition to a BLAKE2b word is homomorphic to `UInt64`
addition. This form is useful between consecutive quarter-round assignments,
where an EVM word is already known only through its low 64 bits. -/
theorem toUInt64_add (x y : UInt256) :
    toUInt64 (x + y) = toUInt64 x + toUInt64 y := by
  apply UInt64.toNat_inj.mp
  rw [toUInt64_toNat, UInt64.toNat_add, toUInt64_toNat, toUInt64_toNat]
  change ((x.val + y.val).val % 2 ^ 64) =
    (x.toNat % 2 ^ 64 + y.toNat % 2 ^ 64) % 2 ^ 64
  rw [Fin.val_add]
  change ((x.toNat + y.toNat) % 2 ^ 256) % 2 ^ 64 = _
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 64 ≤ 256))]
  exact Nat.add_mod _ _ _

theorem mask64_add_words (x y : UInt256) :
    mask64 (x + y) = ofUInt64 (toUInt64 x + toUInt64 y) := by
  rw [mask64_eq_ofUInt64, toUInt64_add]

@[simp] theorem mask64_add3 (x y z : UInt64) :
    mask64 (ofUInt64 x + ofUInt64 y + ofUInt64 z) =
      ofUInt64 (x + y + z) := by
  rw [mask64_eq_ofUInt64, toUInt64_add, toUInt64_add]
  simp

theorem mask64_or (x y : UInt256) :
    mask64 (x ||| y) = ofUInt64 (toUInt64 x ||| toUInt64 y) := by
  apply word_ext
  rw [mask64_toNat, ofUInt64_toNat, UInt64.toNat_or,
    toUInt64_toNat, toUInt64_toNat]
  change (((x.toNat ||| y.toNat) % UInt256.size) &&& 0xffffffffffffffff) = _
  rw [show 0xffffffffffffffff = 2 ^ 64 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod,
    show UInt256.size = 2 ^ 256 by rfl,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)),
    Nat.or_mod_two_pow]

theorem toUInt64_shiftRight_ofUInt64 (x : UInt64) (n : Nat) (hn : n < 64) :
    toUInt64 (UInt256.shiftRight (ofUInt64 x) (UInt256.ofNat n)) =
      x >>> UInt64.ofNat n := by
  apply UInt64.toNat_inj.mp
  rw [toUInt64_toNat]
  have hn256 : n < 256 := by omega
  rw [Challenge.EvmProof.Word.shiftRight_toNat (ofUInt64 x) hn256,
    ofUInt64_toNat, UInt64.toNat_shiftRight, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (Nat.lt_trans hn (by norm_num)),
    Nat.mod_eq_of_lt hn]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.toNat_lt)

theorem shiftRight_ofUInt64 (x : UInt64) (n : Nat) (hn : n < 64) :
    UInt256.shiftRight (ofUInt64 x) (UInt256.ofNat n) =
      ofUInt64 (x >>> UInt64.ofNat n) := by
  apply word_ext
  have hn256 : n < 256 := by omega
  rw [Challenge.EvmProof.Word.shiftRight_toNat (ofUInt64 x) hn256,
    ofUInt64_toNat, ofUInt64_toNat, UInt64.toNat_shiftRight,
    UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (Nat.lt_trans hn (by norm_num))]
  rw [Nat.mod_eq_of_lt hn]

theorem toUInt64_shiftLeft_ofUInt64 (x : UInt64) (n : Nat) (hn : n < 64) :
    toUInt64 (UInt256.shiftLeft (ofUInt64 x) (UInt256.ofNat n)) =
      x <<< UInt64.ofNat n := by
  apply UInt64.toNat_inj.mp
  rw [toUInt64_toNat]
  unfold UInt256.shiftLeft
  have hn256 : (UInt256.ofNat n).toNat = n := by
    rw [word_toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hn (by norm_num))]
  rw [if_neg (by omega), hn256, word_toNat_ofNat,
    show UInt256.size = 2 ^ 256 by rfl,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)), ofUInt64_toNat,
    UInt64.toNat_shiftLeft, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (Nat.lt_trans hn (by norm_num)),
    Nat.mod_eq_of_lt hn]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

/-- The masked `SHR/SHL/OR` idiom in the reference is BLAKE2b's rotation. -/
theorem evm_rotr64 (x : UInt64) (n : Nat) (hn0 : 0 < n) (hn : n < 64) :
    mask64
      (UInt256.shiftRight (ofUInt64 x) (UInt256.ofNat n) |||
       UInt256.shiftLeft (ofUInt64 x) (UInt256.ofNat (64 - n))) =
      ofUInt64 (Crypto.Blake2f.rotr64 x (UInt64.ofNat n)) := by
  rw [mask64_or, toUInt64_shiftRight_ofUInt64 x n hn,
    toUInt64_shiftLeft_ofUInt64 x (64 - n) (by omega)]
  unfold Crypto.Blake2f.rotr64
  have hsub : (64 : UInt64) - UInt64.ofNat n = UInt64.ofNat (64 - n) := by
    simpa using (UInt64.ofNat_sub (a := 64) (b := n) (by omega)).symm
  rw [hsub]

end Challenge.Blake2f.ProofSupport.Word
