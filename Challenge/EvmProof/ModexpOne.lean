import Challenge.EvmProof.ModPow

set_option warningAsError true

/-! # Fixed-layout MODEXP with exponent one -/

namespace Challenge.EvmProof.ModexpOne

open EvmSemantics.EVM

/-- The Osaka MODEXP call used for fixed-width reduction of a 96-byte value
modulo a 48-byte modulus. -/
theorem runModexp_96_1_48 {input : ByteArray} {base modulus : Nat}
    (hbaseSize : Precompile.bytesToNatPadded input 0 32 = 96)
    (hexponentSize : Precompile.bytesToNatPadded input 32 32 = 1)
    (hmodulusSize : Precompile.bytesToNatPadded input 64 32 = 48)
    (hbase : Precompile.bytesToNatPadded input 96 96 = base)
    (hexponent : Precompile.bytesToNatPadded input 192 1 = 1)
    (hmodulus : Precompile.bytesToNatPadded input 193 48 = modulus)
    (hmodulusOne : 1 < modulus) :
    Precompile.runModexp .Osaka input 500 =
      .success (Precompile.natToBytes (base % modulus) 48) 500 := by
  unfold Precompile.runModexp
  rw [hbaseSize, hexponentSize, hmodulusSize]
  simp only [Nat.min_eq_left (by omega : 1 ≤ 32), Nat.reduceAdd]
  rw [hexponent]
  have hnotLarge :
      Precompile.modexpOsakaInputTooLarge 96 1 48 = false := by decide
  simp only [hnotLarge, Bool.false_eq_true, and_false, if_false]
  have hcost : Precompile.modexpGas .Osaka 96 1 48 1 = 500 := by decide
  rw [hcost]
  norm_num
  rw [hbase, hmodulus]
  rw [Challenge.EvmProof.ModPow.eval_eq,
    if_neg (by omega : modulus ≠ 0), pow_one]

end Challenge.EvmProof.ModexpOne
