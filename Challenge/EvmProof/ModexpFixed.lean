import Challenge.EvmProof.ModPow

set_option warningAsError true

/-! # Fixed-width MODEXP execution

Reusable execution facts for fixed-width MODEXP calls. Concrete callers remain
responsible for certifying the exponent head and its fork-specific gas cost.
-/

namespace Challenge.EvmProof.ModexpFixed

open EvmSemantics.EVM

/-- An Osaka MODEXP call with three 48-byte operands, at its certified exact
gas cost, returns the fast modular-exponentiation result in 48 bytes. -/
theorem runModexp_48_48_48 {input : ByteArray}
    {base exponent modulus expHead cost : Nat}
    (hbaseSize : Precompile.bytesToNatPadded input 0 32 = 48)
    (hexponentSize : Precompile.bytesToNatPadded input 32 32 = 48)
    (hmodulusSize : Precompile.bytesToNatPadded input 64 32 = 48)
    (hbase : Precompile.bytesToNatPadded input 96 48 = base)
    (hexponent : Precompile.bytesToNatPadded input 144 48 = exponent)
    (hmodulus : Precompile.bytesToNatPadded input 192 48 = modulus)
    (hexponentHead : Precompile.bytesToNatPadded input 144 32 = expHead)
    (hcost : Precompile.modexpGas .Osaka 48 48 48 expHead = cost) :
    Precompile.runModexp .Osaka input cost =
      .success (Precompile.natToBytes
        (Precompile.modPow base exponent modulus) 48) cost := by
  unfold Precompile.runModexp
  rw [hbaseSize, hexponentSize, hmodulusSize]
  simp only [Nat.min_eq_right (by omega : 32 ≤ 48), Nat.reduceAdd]
  rw [hexponentHead]
  have hnotLarge :
      Precompile.modexpOsakaInputTooLarge 48 48 48 = false := by decide
  simp only [hnotLarge, Bool.false_eq_true, and_false, if_false]
  rw [hcost]
  norm_num
  rw [hbase, hexponent, hmodulus]

end Challenge.EvmProof.ModexpFixed
