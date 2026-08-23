import Mathlib.Data.Nat.Digits.Lemmas

set_option warningAsError true

/-! Generic natural-number digit facts used by direct source-Yul proofs. -/

namespace Challenge.YulProof.NatDigits

theorem getElem_eq_div_mod_ofDigits (radix : Nat) (digits : List Nat)
    (index : Nat) (hradix : 0 < radix) (hindex : index < digits.length)
    (hdigits : ∀ digit ∈ digits, digit < radix) :
    digits[index] = Nat.ofDigits radix digits / radix ^ index % radix := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop index hradix digits hdigits]
  rw [List.drop_eq_getElem_cons hindex]
  simp only [Nat.ofDigits_cons]
  rw [Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (hdigits digits[index] (List.getElem_mem hindex))]

theorem extractedWordByte (value limb rem : Nat) (hrem : rem < 32) :
    ((value / (256 ^ 32) ^ limb % (256 ^ 32)) / 256 ^ rem) % 256 =
      value / 256 ^ (32 * limb + rem) % 256 := by
  let head := value / 256 ^ (32 * limb)
  have hsplit : 256 ^ 32 = 256 ^ rem * 256 ^ (32 - rem) := by
    rw [← Nat.pow_add]
    rw [Nat.add_sub_of_le (Nat.le_of_lt hrem)]
  have hdiv : value / 256 ^ (32 * limb) / 256 ^ rem =
      value / 256 ^ (32 * limb + rem) := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [show (256 ^ 32) ^ limb = 256 ^ (32 * limb) by rw [Nat.pow_mul]]
  change ((head % 256 ^ 32) / 256 ^ rem) % 256 = _
  rw [hsplit, Nat.mod_mul_right_div_self]
  have hdvd : 256 ∣ 256 ^ (32 - rem) :=
    dvd_pow_self 256 (Nat.sub_pos_of_lt hrem).ne'
  rw [Nat.mod_mod_of_dvd _ hdvd]
  exact congrArg (fun n => n % 256) hdiv

end Challenge.YulProof.NatDigits
