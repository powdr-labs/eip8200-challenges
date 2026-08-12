import Challenge.Modexp.Reference.Proofs.Algorithm
import Challenge.EvmProof.Limbs

set_option warningAsError true

/-!
# Compatibility import

The implementation-independent limb theory now lives in
`Challenge.EvmProof.Limbs`.  This compatibility namespace preserves the
established `Limbs.*` API for MODEXP proof modules and downstream imports.
-/

namespace Challenge.Modexp.Reference.Proofs.Limbs

export Challenge.EvmProof.Limbs
  (radix limbCount limbDigits digits memoryLimbs Represents splitTwo joinTwo
   join_splitTwo radix_eq radix_gt_one radix_pos splitTwo_low_lt splitTwo_high_lt
   limbCount_le_32 width_le_limbs limbCount_pos pow_radix byteValue_fits
   length_limbDigits limbDigits_lt value_limbDigits memoryLimb_lt
   length_memoryLimbs value_of_represents represents_value_unique
   represents_iff_value masked_sum_lt_twice masked_sum_lt_twice_of_le
   mod_eq_cond_sub masked_sum_mod_eq_cond_sub useSub_iff addDigitLists
   length_addDigitLists_left addDigitLists_value addDigitLists_append_single
   addDigitLists_digits_lt addDigitLists_carry_le_one ofDigits_map_mul
   addDigitLists_masked_value_mod addDigitLists_masked_carry_le_one addCarryBits
   subDigitLists subDigitLists_append_single subDigitLists_value
   subDigitLists_borrow_le_one subDigitLists_digits_lt subLimbBits)

/-- Backwards-compatible name for the generic fixed-width byte bound. -/
theorem byteValue_fits_limbs (input : ByteArray) (offset width : Nat) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded input offset width <
      radix ^ limbCount width :=
  Challenge.EvmProof.Limbs.byteValue_fits input offset width

end Challenge.Modexp.Reference.Proofs.Limbs
