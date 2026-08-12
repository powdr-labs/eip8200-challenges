import Challenge.EvmProof.Limbs

set_option warningAsError true

namespace Checks.EvmProofWideMul

open EvmSemantics
open Challenge.EvmProof

example (a b : UInt256) :
    (a * b).toNat = (a.toNat * b.toNat) % 2 ^ 256 :=
  Word.word_toNat_mul a b

example (base x y z : Nat) :
    Nat.ofDigits base [x, y, z] = x + base * y + base ^ 2 * z :=
  Limbs.ofDigits_three base x y z

example (x y z : UInt256) :
    x.toNat + Limbs.radix * y.toNat + Limbs.radix ^ 2 * z.toNat <
      Limbs.radix ^ 3 :=
  Limbs.threeWords_lt x y z

example (words : Limbs.WideProduct) :
    words.value < Limbs.radix ^ 2 :=
  Limbs.WideProduct.value_lt words

example (base value : Nat) (hbase : 0 < base) :
    Limbs.joinAt base (Limbs.splitAt base value) = value :=
  Limbs.join_splitAt hbase value

example {base lo hi : Nat} (hbase : 1 < base)
    (hlo : lo < base) (hhi : hi < base) :
    lo + base * hi < base ^ 2 :=
  Limbs.twoDigits_lt hbase hlo hhi

example (base a b : Nat) (hbase : 0 < base) :
    Limbs.joinAt base (Limbs.mulSplit base a b) = a * b :=
  Limbs.join_mulSplit hbase a b

example (base x y z : Nat) (hbase : 0 < base)
    (hx : x < base) (hy : y < base) (hz : z < base) :
    Limbs.joinAt base (Limbs.addThreeAt base x y z) = x + y + z :=
  Limbs.join_addThreeAt hbase hx hy hz

example {base a b c : Nat} (hbase : 0 < base)
    (ha : a < base) (hb : b < base) (hc : c < base) :
    a * b + c < base ^ 2 :=
  Limbs.mul_add_lt_sq hbase ha hb hc

example {base a b c : Nat} (hbase : 0 < base)
    (ha : a < base) (hb : b < base) (hc : c < base) :
    a * b + c < base * base :=
  Limbs.mul_add_lt_mul_self hbase ha hb hc

example {base t0 t1 t2 m n0 n1 carry low1 high1
    sum1 carry1 sum2 carry2 : Nat}
    (hcarry : base * carry = t0 + m * n0)
    (hprod1 : low1 + base * high1 = m * n1)
    (hsum1 : sum1 + base * carry1 = t1 + low1)
    (hsum2 : sum2 + base * carry2 = sum1 + carry) :
    base * (sum2 + base * (t2 + high1 + carry1 + carry2)) =
      t0 + base * t1 + base * base * t2 + m * (n0 + base * n1) :=
  Limbs.ciosReduction_reconstruct hcarry hprod1 hsum1 hsum2

example {base t0 t1 m n0 n1 low0 carry low1 high1
    sum1 carry1 sum2 carry2 : Nat}
    (hcarry : low0 + base * carry = t0 + m * n0)
    (hprod1 : low1 + base * high1 = m * n1)
    (hsum1 : sum1 + base * carry1 = t1 + low1)
    (hsum2 : sum2 + base * carry2 = sum1 + carry) :
    low0 + base * (sum2 + base * (high1 + carry1 + carry2)) =
      t0 + base * t1 + m * (n0 + base * n1) :=
  Limbs.ciosAccumulate_reconstruct hcarry hprod1 hsum1 hsum2

example {base x0 x1 y modulus first second m0 m1 : Nat}
    (hfirst : base * first = x0 * y + m0 * modulus)
    (hsecond : base * second = first + x1 * y + m1 * modulus) :
    base * base * second =
      (x0 + base * x1) * y + (m0 + base * m1) * modulus :=
  Limbs.ciosTwoStep_reconstruct hfirst hsecond

example (a b : UInt256) :
    Limbs.WideProduct.value (Limbs.fullMul256 a b) = a.toNat * b.toNat :=
  Limbs.fullMul256_value a b

example (a : Limbs.WideProduct) (hdouble : 2 * a.value < Limbs.radix ^ 2) :
    (Limbs.doubleWide256 a).value = 2 * a.value :=
  Limbs.doubleWide256_value a hdouble

example (a b : Limbs.WideProduct) :
    (Limbs.subWide256 a b).value =
      if b.value ≤ a.value then a.value - b.value
      else Limbs.radix ^ 2 + a.value - b.value :=
  Limbs.subWide256_value a b

example (a b : Limbs.WideProduct) :
    (Limbs.subWide256 a b).value =
      (a.value + Limbs.radix ^ 2 - b.value) % Limbs.radix ^ 2 :=
  Limbs.subWide256_value_mod a b

example (a b : Limbs.WideProduct) :
    (Limbs.addWide256 a b).value =
      (a.value + b.value) % Limbs.radix ^ 2 :=
  Limbs.addWide256_value_mod a b

example (a b : Limbs.WideProduct) :
    (Limbs.wideGeWord a b).toNat ≠ 0 ↔ b.value ≤ a.value :=
  Limbs.wideGeWord_nonzero_iff a b

example (a b : Limbs.WideProduct) :
    (Limbs.conditionalSubWide256 a b).value =
      if b.value ≤ a.value then a.value - b.value else a.value :=
  Limbs.conditionalSubWide256_value a b

example (a b : Limbs.WideProduct) :
    (Limbs.mulWideLow256 a b).value =
      (a.value * b.value) % Limbs.radix ^ 2 :=
  Limbs.mulWideLow256_value a b

example (x y z : UInt256) :
    (Limbs.addThree256 x y z).value = x.toNat + y.toNat + z.toNat :=
  Limbs.addThree256_value x y z

example (x y : UInt256) :
    (Limbs.addTwo256 x y).value = x.toNat + y.toNat :=
  Limbs.addTwo256_value x y

example (x y : UInt256) : (Limbs.addTwo256 x y).carry.toNat < 2 :=
  Limbs.addTwo256_carry_lt_two x y

example (x y : UInt256) (hzero : x.toNat + y.toNat ≡ 0 [MOD Limbs.radix]) :
    (Limbs.addTwo256 x y).word = UInt256.ofNat 0 :=
  Limbs.addTwo256_word_eq_zero_of_modEq x y hzero

example (x y z : UInt256) :
    (Limbs.addThree256 x y z).carry.toNat < 3 :=
  Limbs.addThree256_carry_lt_three x y z

example (sum : Limbs.WordSum) (term : UInt256)
    (hcarry : sum.carry.toNat + 1 < Limbs.radix) :
    (sum.add term).value = sum.value + term.toNat :=
  Limbs.WordSum.value_add sum term hcarry

example (sum : Limbs.WordSum) (term : UInt256)
    (hcarry : sum.carry.toNat + 1 < Limbs.radix) :
    (sum.add term).carry.toNat ≤ sum.carry.toNat + 1 :=
  Limbs.WordSum.carry_add_le sum term hcarry

example (a b : UInt256) :
    (Limbs.fullMul256 a b).lo.toNat < Limbs.radix ∧
      (Limbs.fullMul256 a b).hi.toNat < Limbs.radix :=
  Limbs.fullMul256_words_lt a b

example (a b : UInt256) :
    (Limbs.fullMul256 a b).hi.toNat < Limbs.radix - 1 :=
  Limbs.fullMul256_hi_lt_pred a b

example (a b : UInt256) :
    (Limbs.fullMul256 a b).hi.toNat ≤ b.toNat :=
  Limbs.fullMul256_hi_le_right a b

/-- info: 'Challenge.EvmProof.Limbs.join_mulSplit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Limbs.join_mulSplit

/-- info: 'Challenge.EvmProof.Limbs.mulSplit_high_eq_mersenne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.mulSplit_high_eq_mersenne

/-- info: 'Challenge.EvmProof.Limbs.fullMul256_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.fullMul256_value

/-- info: 'Challenge.EvmProof.Limbs.join_addThreeAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.join_addThreeAt

/-- info: 'Challenge.EvmProof.Limbs.mul_add_lt_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.mul_add_lt_sq

/-- info: 'Challenge.EvmProof.Limbs.mul_add_lt_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.mul_add_lt_mul_self

/-- info: 'Challenge.EvmProof.Limbs.ciosReduction_reconstruct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.ciosReduction_reconstruct

/-- info: 'Challenge.EvmProof.Limbs.ciosAccumulate_reconstruct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.ciosAccumulate_reconstruct

/-- info: 'Challenge.EvmProof.Limbs.ciosTwoStep_reconstruct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.ciosTwoStep_reconstruct

/-- info: 'Challenge.EvmProof.Limbs.addThree256_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.addThree256_value

/-- info: 'Challenge.EvmProof.Limbs.addThree256_carry_lt_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.addThree256_carry_lt_three

/-- info: 'Challenge.EvmProof.Limbs.WordSum.value_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.WordSum.value_add

/-- info: 'Challenge.EvmProof.Limbs.WordSum.carry_add_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.WordSum.carry_add_le

/-- info: 'Challenge.EvmProof.Limbs.ofDigits_three' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Limbs.ofDigits_three

/-- info: 'Challenge.EvmProof.Limbs.threeWords_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.threeWords_lt

/-- info: 'Challenge.EvmProof.Limbs.WideProduct.value_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.WideProduct.value_lt

/-- info: 'Challenge.EvmProof.Limbs.subWide256_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.subWide256_value

/-- info: 'Challenge.EvmProof.Limbs.subWide256_value_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.subWide256_value_mod

/-- info: 'Challenge.EvmProof.Word.word_toNat_mul' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Word.word_toNat_mul

/-- info: 'Challenge.EvmProof.Limbs.mulWideLow256_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.mulWideLow256_value

/-- info: 'Challenge.EvmProof.Word.word_toNat_gt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Word.word_toNat_gt

/-- info: 'Challenge.EvmProof.Word.word_toNat_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Word.word_toNat_eq

/-- info: 'Challenge.EvmProof.Limbs.wideGeWord_nonzero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.wideGeWord_nonzero_iff

/-- info: 'Challenge.EvmProof.Limbs.conditionalSubWide256_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.conditionalSubWide256_value

/-- info: 'Challenge.EvmProof.Word.shiftLeft_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Word.shiftLeft_toNat

/-- info: 'Challenge.EvmProof.Limbs.doubleWide256_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.doubleWide256_value

/-- info: 'Challenge.EvmProof.Limbs.addTwo256_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.addTwo256_value

/-- info: 'Challenge.EvmProof.Limbs.addTwo256_carry_lt_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.addTwo256_carry_lt_two

/-- info: 'Challenge.EvmProof.Limbs.addTwo256_word_eq_zero_of_modEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Limbs.addTwo256_word_eq_zero_of_modEq

/-- info: 'Challenge.EvmProof.Limbs.join_splitAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Limbs.join_splitAt

/-- info: 'Challenge.EvmProof.Limbs.splitAt_low_lt' does not depend on any axioms -/
#guard_msgs in
#print axioms Limbs.splitAt_low_lt

/-- info: 'Challenge.EvmProof.Limbs.mulSplit_high_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.mulSplit_high_lt

/-- info: 'Challenge.EvmProof.Limbs.fullMul256_words_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Limbs.fullMul256_words_lt

/-- info: 'Challenge.EvmProof.Limbs.twoDigits_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.twoDigits_lt

/-- info: 'Challenge.EvmProof.Limbs.residual_eq_mod_of_eq_add' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Limbs.residual_eq_mod_of_eq_add

/-- info: 'Challenge.EvmProof.Limbs.addWide256_value_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.addWide256_value_mod

/-- info: 'Challenge.EvmProof.Limbs.fullMul256_hi_lt_pred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.fullMul256_hi_lt_pred

/-- info: 'Challenge.EvmProof.Limbs.fullMul256_hi_le_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Limbs.fullMul256_hi_le_right

end Checks.EvmProofWideMul
