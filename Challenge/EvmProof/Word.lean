import EvmSemantics.Crypto.Sha256
import EvmSemantics.Crypto.Ripemd160
import EvmSemantics.Data.UInt256
import Init.Data.Fin.Bitwise
import Mathlib.Tactic.NormNum
set_option warningAsError true
/-!
# 32-bit words inside the EVM word type

SHA-256 is a 32-bit algorithm, whereas every EVM arithmetic and bitwise
opcode works on 256-bit words.  This file is the reusable boundary between
those two representations.  It deliberately has no dependency on the Yul
compiler or on the reference bytecode.
-/

namespace Challenge.EvmProof.Word

/-- Embed a SHA word in the low 32 bits of an EVM word. -/
def ofUInt32 (x : UInt32) : EvmSemantics.UInt256 :=
  EvmSemantics.UInt256.ofNat x.toNat

/-- Project the low 32 bits of an EVM word. -/
def toUInt32 (x : EvmSemantics.UInt256) : UInt32 := UInt32.ofNat x.toNat

/-- The EVM expression used by the reference program to truncate to a SHA
word. -/
def mask32 (x : EvmSemantics.UInt256) : EvmSemantics.UInt256 :=
  x &&& EvmSemantics.UInt256.ofNat 0xffffffff

theorem word_ext {a b : EvmSemantics.UInt256} (h : a.toNat = b.toNat) : a = b := by
  cases a
  cases b
  exact congrArg EvmSemantics.UInt256.mk (Fin.ext h)

theorem word_add_comm (a b : EvmSemantics.UInt256) : a + b = b + a := by
  apply word_ext
  change (a.val + b.val).val = (b.val + a.val).val
  rw [Fin.val_add, Fin.val_add, Nat.add_comm]

theorem word_toNat_add (a b : EvmSemantics.UInt256) :
    (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 256 := by
  change (a.val + b.val).val = _
  rw [Fin.val_add]
  rfl

theorem word_toNat_sub (a b : EvmSemantics.UInt256) :
    (a - b).toNat = (2 ^ 256 + a.toNat - b.toNat) % 2 ^ 256 := by
  change (a.val - b.val).val = _
  rw [Fin.val_sub]
  change (EvmSemantics.UInt256.size - b.toNat + a.toNat) %
      EvmSemantics.UInt256.size = _
  congr 1
  change 2 ^ 256 - b.toNat + a.toNat = 2 ^ 256 + a.toNat - b.toNat
  have hb : b.toNat < 2 ^ 256 := b.val.isLt
  omega

theorem word_toNat_sub_cond (a b : EvmSemantics.UInt256) :
    (a - b).toNat =
      if a.toNat < b.toNat then 2 ^ 256 + a.toNat - b.toNat
      else a.toNat - b.toNat := by
  rw [word_toNat_sub]
  by_cases hab : a.toNat < b.toNat
  · rw [if_pos hab, Nat.mod_eq_of_lt]
    have ha : a.toNat < 2 ^ 256 := a.val.isLt
    have hb : b.toNat < 2 ^ 256 := b.val.isLt
    omega
  · rw [if_neg hab]
    have hb : b.toNat < 2 ^ 256 := b.val.isLt
    have hrearrange : 2 ^ 256 + a.toNat - b.toNat =
        2 ^ 256 + (a.toNat - b.toNat) := by omega
    have hdifference : a.toNat - b.toNat < 2 ^ 256 :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.val.isLt
    rw [hrearrange, Nat.add_mod, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt hdifference]
    exact Nat.mod_eq_of_lt hdifference

theorem word_toNat_lt (a b : EvmSemantics.UInt256) :
    (EvmSemantics.UInt256.lt a b).toNat =
      if a.toNat < b.toNat then 1 else 0 := by
  simp only [EvmSemantics.UInt256.lt]
  split <;> norm_num [EvmSemantics.UInt256.ofNat,
    EvmSemantics.UInt256.toNat, EvmSemantics.UInt256.size]

theorem word_toNat_isZero (a : EvmSemantics.UInt256) :
    a.isZero.toNat = if a.toNat = 0 then 1 else 0 := by
  simp only [EvmSemantics.UInt256.isZero]
  split <;> norm_num [EvmSemantics.UInt256.ofNat,
    EvmSemantics.UInt256.toNat, EvmSemantics.UInt256.size]

theorem word_toNat_lor (a b : EvmSemantics.UInt256) :
    (EvmSemantics.UInt256.lor a b).toNat = a.toNat ||| b.toNat := by
  change (a.val ||| b.val).val = _
  rw [Fin.or_val]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_lt_of_le
    (Nat.or_lt_two_pow a.val.isLt b.val.isLt) (by rfl)

theorem word_toNat_land (a b : EvmSemantics.UInt256) :
    (EvmSemantics.UInt256.land a b).toNat = a.toNat &&& b.toNat := by
  change (a.val &&& b.val).val = _
  rw [Fin.and_val]
  rfl

@[simp] theorem word_toNat_ofNat (n : Nat) :
    (EvmSemantics.UInt256.ofNat n).toNat = n % 2 ^ 256 := by
  simp [EvmSemantics.UInt256.ofNat, EvmSemantics.UInt256.toNat,
    EvmSemantics.UInt256.size]

theorem word_eq_ofNat_toNat (a : EvmSemantics.UInt256) :
    a = EvmSemantics.UInt256.ofNat a.toNat := by
  apply word_ext
  rw [word_toNat_ofNat]
  exact (Nat.mod_eq_of_lt a.val.isLt).symm

/-- Normalize elaborated `UInt256` numeral syntax to the explicit constructor.
This lets symbolic traces reuse the arithmetic lemmas below even when a frozen
instruction artifact stores PUSH immediates using numeral notation. -/
theorem literal_eq_ofNat (n : Nat) :
    (OfNat.ofNat n : EvmSemantics.UInt256) = EvmSemantics.UInt256.ofNat n := rfl

theorem ofNat_add_ofNat {a b : Nat} (h : a + b < 2 ^ 256) :
    EvmSemantics.UInt256.ofNat a + EvmSemantics.UInt256.ofNat b =
      EvmSemantics.UInt256.ofNat (a + b) := by
  apply word_ext
  change ((EvmSemantics.UInt256.ofNat a).val +
    (EvmSemantics.UInt256.ofNat b).val).val = _
  rw [Fin.val_add]
  change ((EvmSemantics.UInt256.ofNat a).toNat +
    (EvmSemantics.UInt256.ofNat b).toNat) %
      EvmSemantics.UInt256.size = _
  have ha : a < 2 ^ 256 := by omega
  have hb : b < 2 ^ 256 := by omega
  rw [word_toNat_ofNat, word_toNat_ofNat, word_toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    show EvmSemantics.UInt256.size = 2 ^ 256 by rfl,
    Nat.mod_eq_of_lt h]

/-- Addition commutes with embedding even when the natural sum wraps.  Both
sides use the same EVM-word modulus, so no range side condition is needed. -/
theorem ofNat_add_mod (a b : Nat) :
    EvmSemantics.UInt256.ofNat a + EvmSemantics.UInt256.ofNat b =
      EvmSemantics.UInt256.ofNat (a + b) := by
  apply word_ext
  change ((EvmSemantics.UInt256.ofNat a).val +
    (EvmSemantics.UInt256.ofNat b).val).val = _
  rw [Fin.val_add]
  change ((a % 2 ^ 256 + b % 2 ^ 256) % 2 ^ 256) =
    (a + b) % 2 ^ 256
  exact (Nat.add_mod a b (2 ^ 256)).symm

/-- Program-counter successor commutes with natural embedding modulo the EVM
word size. -/
theorem succ_ofNat_mod (n : Nat) :
    (EvmSemantics.UInt256.ofNat n).succ =
      EvmSemantics.UInt256.ofNat (n + 1) := by
  exact ofNat_add_mod n 1

theorem ofNat_sub_ofNat {a b : Nat} (hba : b ≤ a) (ha : a < 2 ^ 256) :
    EvmSemantics.UInt256.ofNat a - EvmSemantics.UInt256.ofNat b =
      EvmSemantics.UInt256.ofNat (a - b) := by
  have hb : b < 2 ^ 256 := Nat.lt_of_le_of_lt hba ha
  have hab : a - b < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
  apply word_ext
  change ((EvmSemantics.UInt256.ofNat a).val -
    (EvmSemantics.UInt256.ofNat b).val).val = _
  rw [Fin.val_sub]
  change (EvmSemantics.UInt256.size -
      (EvmSemantics.UInt256.ofNat b).toNat +
      (EvmSemantics.UInt256.ofNat a).toNat) %
      EvmSemantics.UInt256.size =
    (EvmSemantics.UInt256.ofNat (a - b)).toNat
  rw [word_toNat_ofNat, word_toNat_ofNat, word_toNat_ofNat,
    Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hab]
  have hrearrange : EvmSemantics.UInt256.size - b + a =
      EvmSemantics.UInt256.size + (a - b) := by
    change 2 ^ 256 - b + a = 2 ^ 256 + (a - b)
    omega
  rw [hrearrange, Nat.add_mod, Nat.mod_self, Nat.zero_add]
  change ((a - b) % 2 ^ 256) % 2 ^ 256 = a - b
  rw [Nat.mod_eq_of_lt hab, Nat.mod_eq_of_lt hab]

theorem succ_ofNat {n : Nat} (h : n + 1 < 2 ^ 256) :
    (EvmSemantics.UInt256.ofNat n).succ =
      EvmSemantics.UInt256.ofNat (n + 1) := by
  exact ofNat_add_ofNat h

@[simp] theorem toUInt32_ofUInt32 (x : UInt32) :
    toUInt32 (ofUInt32 x) = x := by
  apply UInt32.toNat_inj.mp
  have hx256 : x.toNat < 2 ^ 256 :=
    Nat.lt_trans x.toNat_lt (by norm_num)
  rw [toUInt32, UInt32.toNat_ofNat', ofUInt32, word_toNat_ofNat,
    Nat.mod_eq_of_lt hx256, Nat.mod_eq_of_lt x.toNat_lt]

@[simp] theorem ofUInt32_toNat (x : UInt32) :
    (ofUInt32 x).toNat = x.toNat := by
  have hx256 : x.toNat < 2 ^ 256 :=
    Nat.lt_trans x.toNat_lt (by norm_num)
  rw [ofUInt32, word_toNat_ofNat, Nat.mod_eq_of_lt hx256]

theorem ofUInt32_injective : Function.Injective ofUInt32 := by
  intro a b h
  apply UInt32.toNat_inj.mp
  simpa using congrArg EvmSemantics.UInt256.toNat h

@[simp] theorem ofUInt32_inj {a b : UInt32} :
    ofUInt32 a = ofUInt32 b ↔ a = b := ofUInt32_injective.eq_iff

@[simp] theorem toUInt32_toNat (x : EvmSemantics.UInt256) :
    (toUInt32 x).toNat = x.toNat % 2 ^ 32 := by
  simp [toUInt32]

@[simp] theorem mask32_toNat (x : EvmSemantics.UInt256) :
    (mask32 x).toNat = x.toNat &&& 0xffffffff := by
  change (x.val &&& (EvmSemantics.UInt256.ofNat 0xffffffff).val).val = _
  rw [Fin.and_val]
  change x.toNat &&& (EvmSemantics.UInt256.ofNat 0xffffffff).toNat = _
  rw [word_toNat_ofNat]
  norm_num

theorem mask32_eq_ofUInt32 (x : EvmSemantics.UInt256) :
    mask32 x = ofUInt32 (toUInt32 x) := by
  apply word_ext
  rw [mask32_toNat, ofUInt32_toNat, toUInt32_toNat]
  rw [show 0xffffffff = 2 ^ 32 - 1 by norm_num]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

@[simp] theorem mask32_ofUInt32 (x : UInt32) :
    mask32 (ofUInt32 x) = ofUInt32 x := by
  rw [mask32_eq_ofUInt32, toUInt32_ofUInt32]

@[simp] theorem mask32_idem (x : EvmSemantics.UInt256) :
    mask32 (mask32 x) = mask32 x := by
  rw [mask32_eq_ofUInt32 x, mask32_ofUInt32]

@[simp] theorem ofUInt32_and (x y : UInt32) :
    ofUInt32 (x &&& y) = ofUInt32 x &&& ofUInt32 y := by
  apply word_ext
  rw [ofUInt32_toNat]
  change (x &&& y).toNat = ((ofUInt32 x).val &&& (ofUInt32 y).val).val
  rw [Fin.and_val]
  rw [UInt32.toNat_and]
  exact congrArg₂ Nat.land (ofUInt32_toNat x).symm (ofUInt32_toNat y).symm

@[simp] theorem ofUInt32_or (x y : UInt32) :
    ofUInt32 (x ||| y) = ofUInt32 x ||| ofUInt32 y := by
  apply word_ext
  rw [ofUInt32_toNat]
  change (x ||| y).toNat =
    ((ofUInt32 x).toNat ||| (ofUInt32 y).toNat) %
      EvmSemantics.UInt256.size
  rw [UInt32.toNat_or, ofUInt32_toNat, ofUInt32_toNat]
  apply Eq.symm
  apply Nat.mod_eq_of_lt
  exact Nat.lt_trans (Nat.or_lt_two_pow x.toNat_lt y.toNat_lt) (by
    change 2 ^ 32 < 2 ^ 256
    norm_num)

@[simp] theorem ofUInt32_xor (x y : UInt32) :
    ofUInt32 (x ^^^ y) = ofUInt32 x ^^^ ofUInt32 y := by
  apply word_ext
  rw [ofUInt32_toNat]
  change (x ^^^ y).toNat =
    ((ofUInt32 x).toNat ^^^ (ofUInt32 y).toNat) %
      EvmSemantics.UInt256.size
  rw [UInt32.toNat_xor, ofUInt32_toNat, ofUInt32_toNat]
  apply Eq.symm
  apply Nat.mod_eq_of_lt
  exact Nat.lt_trans (Nat.xor_lt_two_pow x.toNat_lt y.toNat_lt) (by
    change 2 ^ 32 < 2 ^ 256
    norm_num)

@[simp] theorem mask32_add (x y : UInt32) :
    mask32 (ofUInt32 x + ofUInt32 y) = ofUInt32 (x + y) := by
  rw [mask32_eq_ofUInt32]
  apply congrArg ofUInt32
  apply UInt32.toNat_inj.mp
  rw [toUInt32_toNat, UInt32.toNat_add]
  change ((ofUInt32 x).val + (ofUInt32 y).val).val % 2 ^ 32 = _
  rw [Fin.val_add]
  change ((ofUInt32 x).toNat + (ofUInt32 y).toNat) %
    EvmSemantics.UInt256.size % 2 ^ 32 = _
  rw [ofUInt32_toNat, ofUInt32_toNat,
    show EvmSemantics.UInt256.size = 2 ^ 256 by rfl,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

@[simp] theorem mask32_add_left (x : UInt32) (y : EvmSemantics.UInt256) :
    mask32 (ofUInt32 x + y) = ofUInt32 (x + toUInt32 y) := by
  rw [mask32_eq_ofUInt32]
  apply congrArg ofUInt32
  apply UInt32.toNat_inj.mp
  rw [toUInt32_toNat, UInt32.toNat_add, toUInt32_toNat]
  change ((ofUInt32 x).val + y.val).val % 2 ^ 32 = _
  rw [Fin.val_add]
  change ((ofUInt32 x).toNat + y.toNat) %
    EvmSemantics.UInt256.size % 2 ^ 32 = _
  rw [ofUInt32_toNat,
    show EvmSemantics.UInt256.size = 2 ^ 256 by rfl,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  exact (Nat.add_mod_mod _ _ _).symm

@[simp] theorem mask32_add_right (x : EvmSemantics.UInt256) (y : UInt32) :
    mask32 (x + ofUInt32 y) = ofUInt32 (toUInt32 x + y) := by
  have hcomm : x + ofUInt32 y = ofUInt32 y + x := by
    apply word_ext
    change (x.val + (ofUInt32 y).val).val = ((ofUInt32 y).val + x.val).val
    simp only [Fin.val_add]
    rw [Nat.add_comm]
  rw [hcomm, mask32_add_left]
  apply congrArg ofUInt32
  apply UInt32.toNat_inj.mp
  simp [Nat.add_comm]

@[simp] theorem toUInt32_add (x y : EvmSemantics.UInt256) :
    toUInt32 (x + y) = toUInt32 x + toUInt32 y := by
  apply UInt32.toNat_inj.mp
  simp only [toUInt32_toNat, UInt32.toNat_add]
  change ((x.val + y.val).val % 2 ^ 32) =
    (x.toNat % 2 ^ 32 + y.toNat % 2 ^ 32) % 2 ^ 32
  rw [Fin.val_add]
  change ((x.toNat + y.toNat) % EvmSemantics.UInt256.size) % 2 ^ 32 = _
  rw [show EvmSemantics.UInt256.size = 2 ^ 256 by rfl,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)), Nat.add_mod]

theorem shiftRight_ofUInt32 (x : UInt32) (n : Nat) (hn : n < 32) :
    EvmSemantics.UInt256.shiftRight
        (ofUInt32 x) (EvmSemantics.UInt256.ofNat n) =
      ofUInt32 (x >>> UInt32.ofNat n) := by
  have hn256 : n < 2 ^ 256 := Nat.lt_trans hn (by norm_num)
  have hshift : (EvmSemantics.UInt256.ofNat n).toNat = n := by
    rw [word_toNat_ofNat, Nat.mod_eq_of_lt hn256]
  apply word_ext
  unfold EvmSemantics.UInt256.shiftRight
  rw [if_neg (by omega)]
  change ((ofUInt32 x).val >>> (EvmSemantics.UInt256.ofNat n).val).val = _
  rw [Fin.shiftRight_val]
  rw [show (ofUInt32 x).val.val = x.toNat by exact ofUInt32_toNat x]
  rw [show (EvmSemantics.UInt256.ofNat n).val.val = n by exact hshift]
  rw [ofUInt32_toNat, UInt32.toNat_shiftRight,
    UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (Nat.lt_trans hn (by norm_num)),
    Nat.mod_eq_of_lt hn]

theorem shiftRight_ofNat {value shift : Nat}
    (hvalue : value < 2 ^ 256) (hshift : shift < 256) :
    EvmSemantics.UInt256.shiftRight
        (EvmSemantics.UInt256.ofNat value)
        (EvmSemantics.UInt256.ofNat shift) =
      EvmSemantics.UInt256.ofNat (value >>> shift) := by
  have hshift256 : shift < 2 ^ 256 :=
    Nat.lt_trans hshift (by norm_num)
  have hshiftWord : (EvmSemantics.UInt256.ofNat shift).toNat = shift := by
    rw [word_toNat_ofNat, Nat.mod_eq_of_lt hshift256]
  apply word_ext
  unfold EvmSemantics.UInt256.shiftRight
  rw [if_neg (by omega)]
  change ((EvmSemantics.UInt256.ofNat value).val >>>
    (EvmSemantics.UInt256.ofNat shift).val).val = _
  rw [Fin.shiftRight_val]
  rw [show (EvmSemantics.UInt256.ofNat value).val.val = value by
        exact (word_toNat_ofNat value).trans (Nat.mod_eq_of_lt hvalue),
      show (EvmSemantics.UInt256.ofNat shift).val.val = shift by
        exact hshiftWord]
  rw [word_toNat_ofNat]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hvalue)]

theorem shiftRight_toNat (value : EvmSemantics.UInt256) {shift : Nat}
    (hshift : shift < 256) :
    (EvmSemantics.UInt256.shiftRight value
      (EvmSemantics.UInt256.ofNat shift)).toNat = value.toNat >>> shift := by
  have hright := shiftRight_ofNat (value := value.toNat) (shift := shift)
    value.val.isLt hshift
  have hshifted : value.toNat >>> shift < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) value.val.isLt
  have hvalue : (EvmSemantics.UInt256.ofNat value.toNat).toNat = value.toNat :=
    (word_toNat_ofNat value.toNat).trans (Nat.mod_eq_of_lt value.val.isLt)
  rw [word_eq_ofNat_toNat value, hright, word_toNat_ofNat,
    Nat.mod_eq_of_lt hshifted, hvalue]

theorem shiftLeft_ofNat {value shift : Nat}
    (hvalue : value < 2 ^ 256) (hshift : shift < 256)
    (hresult : value * 2 ^ shift < 2 ^ 256) :
    EvmSemantics.UInt256.shiftLeft
        (EvmSemantics.UInt256.ofNat value)
        (EvmSemantics.UInt256.ofNat shift) =
      EvmSemantics.UInt256.ofNat (value * 2 ^ shift) := by
  have hshift256 : shift < 2 ^ 256 :=
    Nat.lt_trans hshift (by norm_num)
  have hshiftWord : (EvmSemantics.UInt256.ofNat shift).toNat = shift := by
    rw [word_toNat_ofNat, Nat.mod_eq_of_lt hshift256]
  unfold EvmSemantics.UInt256.shiftLeft
  rw [if_neg (by omega), hshiftWord, word_toNat_ofNat,
    Nat.mod_eq_of_lt hvalue, Nat.shiftLeft_eq,
    show EvmSemantics.UInt256.size = 2 ^ 256 by rfl,
    Nat.mod_eq_of_lt hresult]

theorem mask32_shiftLeft_ofUInt32 (x : UInt32) (n : Nat) (hn : n < 32) :
    mask32 (EvmSemantics.UInt256.shiftLeft
        (ofUInt32 x) (EvmSemantics.UInt256.ofNat n)) =
      ofUInt32 (x <<< UInt32.ofNat n) := by
  have hn256 : n < 2 ^ 256 := Nat.lt_trans hn (by norm_num)
  have hshift : (EvmSemantics.UInt256.ofNat n).toNat = n := by
    rw [word_toNat_ofNat, Nat.mod_eq_of_lt hn256]
  rw [mask32_eq_ofUInt32]
  apply congrArg ofUInt32
  apply UInt32.toNat_inj.mp
  rw [toUInt32_toNat]
  unfold EvmSemantics.UInt256.shiftLeft
  rw [if_neg (by omega)]
  rw [word_toNat_ofNat]
  rw [hshift]
  rw [show EvmSemantics.UInt256.size = 2 ^ 256 by rfl, Nat.mod_mod]
  rw [ofUInt32_toNat,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)),
    UInt32.toNat_shiftLeft, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (Nat.lt_trans hn (by norm_num)),
    Nat.mod_eq_of_lt hn]

theorem mask32_or (x y : EvmSemantics.UInt256) :
    mask32 (x ||| y) = ofUInt32 (toUInt32 x ||| toUInt32 y) := by
  apply word_ext
  rw [mask32_toNat, ofUInt32_toNat, UInt32.toNat_or,
    toUInt32_toNat, toUInt32_toNat]
  change (((x.toNat ||| y.toNat) % EvmSemantics.UInt256.size) &&&
    0xffffffff) = _
  rw [show 0xffffffff = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod,
    show EvmSemantics.UInt256.size = 2 ^ 256 by rfl,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)),
    Nat.or_mod_two_pow]

theorem mask32_xor (x y : EvmSemantics.UInt256) :
    mask32 (x ^^^ y) = ofUInt32 (toUInt32 x ^^^ toUInt32 y) := by
  apply word_ext
  rw [mask32_toNat, ofUInt32_toNat, UInt32.toNat_xor,
    toUInt32_toNat, toUInt32_toNat]
  change (((x.toNat ^^^ y.toNat) % EvmSemantics.UInt256.size) &&&
    0xffffffff) = _
  rw [show 0xffffffff = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod,
    show EvmSemantics.UInt256.size = 2 ^ 256 by rfl,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)),
    Nat.xor_mod_two_pow]

@[simp] theorem toUInt32_or (x y : EvmSemantics.UInt256) :
    toUInt32 (x ||| y) = toUInt32 x ||| toUInt32 y := by
  apply ofUInt32_injective
  rw [← mask32_eq_ofUInt32, mask32_or]

@[simp] theorem toUInt32_xor (x y : EvmSemantics.UInt256) :
    toUInt32 (x ^^^ y) = toUInt32 x ^^^ toUInt32 y := by
  apply ofUInt32_injective
  rw [← mask32_eq_ofUInt32, mask32_xor]

theorem mask32_and (x y : EvmSemantics.UInt256) :
    mask32 (x &&& y) = ofUInt32 (toUInt32 x &&& toUInt32 y) := by
  apply word_ext
  rw [mask32_toNat, ofUInt32_toNat, UInt32.toNat_and,
    toUInt32_toNat, toUInt32_toNat]
  change (((x.toNat &&& y.toNat) % EvmSemantics.UInt256.size) &&&
    0xffffffff) = _
  rw [show 0xffffffff = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod,
    show EvmSemantics.UInt256.size = 2 ^ 256 by rfl,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)),
    Nat.and_mod_two_pow]

theorem and_ofUInt32 (x : EvmSemantics.UInt256) (y : UInt32) :
    x &&& ofUInt32 y = ofUInt32 (toUInt32 x &&& y) := by
  apply word_ext
  change (x.val &&& (ofUInt32 y).val).val = _
  rw [Fin.and_val,
    show (ofUInt32 y).val.val = y.toNat by exact ofUInt32_toNat y,
    ofUInt32_toNat, UInt32.toNat_and, toUInt32_toNat]
  change x.toNat &&& y.toNat = x.toNat % 2 ^ 32 &&& y.toNat
  calc
    x.toNat &&& y.toNat = (x.toNat &&& y.toNat) % 2 ^ 32 :=
      (Nat.mod_eq_of_lt
        (Nat.lt_of_le_of_lt Nat.and_le_right y.toNat_lt)).symm
    _ = x.toNat % 2 ^ 32 &&& y.toNat % 2 ^ 32 := Nat.and_mod_two_pow
    _ = x.toNat % 2 ^ 32 &&& y.toNat := by
      rw [Nat.mod_eq_of_lt y.toNat_lt]

theorem toUInt32_not_ofUInt32 (x : UInt32) :
    toUInt32 (~~~ofUInt32 x) = x ^^^ 0xffffffff := by
  apply UInt32.toNat_inj.mp
  rw [toUInt32_toNat]
  change (EvmSemantics.UInt256.lnot (ofUInt32 x)).toNat % 2 ^ 32 = _
  unfold EvmSemantics.UInt256.lnot
  rw [word_toNat_ofNat,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  rw [ofUInt32_toNat]
  have hx : x.toNat < 2 ^ 32 := x.toNat_lt
  have hdecomp :
      2 ^ 256 - 1 - x.toNat =
        (2 ^ 256 - 2 ^ 32) + (2 ^ 32 - 1 - x.toNat) := by
    omega
  rw [show EvmSemantics.UInt256.size = 2 ^ 256 by rfl, hdecomp,
    Nat.add_mod]
  have hmultiple : 2 ^ 32 ∣ 2 ^ 256 - 2 ^ 32 := by
    norm_num
  rw [Nat.mod_eq_zero_of_dvd hmultiple, Nat.zero_add,
    Nat.mod_eq_of_lt (by omega)]
  have hall : (0xffffffff : UInt32) = -1 := by decide
  rw [hall, UInt32.xor_neg_one, UInt32.toNat_not]
  rw [show UInt32.size = 2 ^ 32 by rfl, Nat.mod_eq_of_lt (by omega)]

theorem toUInt32_shiftRight_ofUInt32 (x : UInt32) (n : Nat) (hn : n < 32) :
    toUInt32 (EvmSemantics.UInt256.shiftRight
      (ofUInt32 x) (EvmSemantics.UInt256.ofNat n)) =
      x >>> UInt32.ofNat n := by
  rw [shiftRight_ofUInt32 x n hn, toUInt32_ofUInt32]

theorem toUInt32_shiftLeft_ofUInt32 (x : UInt32) (n : Nat) (hn : n < 32) :
    toUInt32 (EvmSemantics.UInt256.shiftLeft
      (ofUInt32 x) (EvmSemantics.UInt256.ofNat n)) =
      x <<< UInt32.ofNat n := by
  have h := mask32_shiftLeft_ofUInt32 x n hn
  rw [mask32_eq_ofUInt32] at h
  exact ofUInt32_injective h

theorem evm_rotr32 (x : UInt32) (n : Nat) (hn0 : 0 < n) (hn : n < 32) :
    mask32
      (EvmSemantics.UInt256.shiftRight
          (ofUInt32 x) (EvmSemantics.UInt256.ofNat n) |||
       EvmSemantics.UInt256.shiftLeft
          (ofUInt32 x) (EvmSemantics.UInt256.ofNat (32 - n))) =
      ofUInt32 (EvmSemantics.Crypto.Sha256.rotr32 x n) := by
  rw [mask32_or, toUInt32_shiftRight_ofUInt32 x n hn,
    toUInt32_shiftLeft_ofUInt32 x (32 - n) (by omega)]
  rfl

/-- The masked EVM `SHL/SHR/OR` idiom used by RIPEMD-160 is exactly a
32-bit left rotation. -/
theorem evm_rotl32 (x : UInt32) (n : Nat) (hn0 : 0 < n) (hn : n < 32) :
    mask32
      (EvmSemantics.UInt256.shiftLeft
          (ofUInt32 x) (EvmSemantics.UInt256.ofNat n) |||
       EvmSemantics.UInt256.shiftRight
          (ofUInt32 x) (EvmSemantics.UInt256.ofNat (32 - n))) =
      ofUInt32 (EvmSemantics.Crypto.Ripemd160.rotl32 x n) := by
  rw [mask32_or, toUInt32_shiftLeft_ofUInt32 x n hn,
    toUInt32_shiftRight_ofUInt32 x (32 - n) (by omega)]
  rfl

end Challenge.EvmProof.Word
