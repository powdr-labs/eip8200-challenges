import Challenge.Bls12381.ProofSupport.FpBarrett

set_option warningAsError true

namespace Checks.Bls12381FpBarrett

open Challenge.Bls12381.ProofSupport

example (product : Fp.SchoolbookProduct) :
    product.value / Challenge.EvmProof.Limbs.radix =
      product.r1.toNat + Challenge.EvmProof.Limbs.radix * product.r2.toNat :=
  Fp.schoolbookHigh_eq_div product

example (product : Fp.SchoolbookProduct) :
    (Fp.barrettQuotient product).value * EvmSemantics.Crypto.Bls12381.p ≤
      product.value :=
  Fp.barrettQuotient_mul_modulus_le product

example (product : Fp.SchoolbookProduct) :
    (product.value -
        (Fp.barrettQuotient product).value * EvmSemantics.Crypto.Bls12381.p) *
        Challenge.EvmProof.Limbs.radix ^ 3 =
      (product.value % Challenge.EvmProof.Limbs.radix) *
          Challenge.EvmProof.Limbs.radix ^ 3 +
        (product.value / Challenge.EvmProof.Limbs.radix) *
          (Challenge.EvmProof.Limbs.radix ^ 4 %
            EvmSemantics.Crypto.Bls12381.p) +
        ((product.value / Challenge.EvmProof.Limbs.radix) * Fp.barrettMu %
            Challenge.EvmProof.Limbs.radix ^ 3) *
          EvmSemantics.Crypto.Bls12381.p :=
  Fp.barrettScaledRemainder_eq product

example (product : Fp.SchoolbookProduct)
    (hproduct : product.value < EvmSemantics.Crypto.Bls12381.p ^ 2) :
    product.value -
        (Fp.barrettQuotient product).value * EvmSemantics.Crypto.Bls12381.p <
      3 * EvmSemantics.Crypto.Bls12381.p :=
  Fp.barrettRemainder_lt_three_mul_modulus product hproduct

example (product : Fp.SchoolbookProduct) :
    (Fp.barrettQuotient product).value =
      ((product.r1.toNat + Challenge.EvmProof.Limbs.radix *
          product.r2.toNat) * Fp.barrettMu) /
        Challenge.EvmProof.Limbs.radix ^ 3 :=
  Fp.value_barrettQuotient product

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettLower_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.barrettLower_lt

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettSchedule_regroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.barrettSchedule_regroup

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettSchedule_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.barrettSchedule_div

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettQuotient_value_eq_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Fp.barrettQuotient_value_eq_schedule

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_barrettQuotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_barrettQuotient

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.schoolbookHigh_eq_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.schoolbookHigh_eq_div

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettQuotient_mul_modulus_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Fp.barrettQuotient_mul_modulus_le

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettScaledRemainder_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Fp.barrettScaledRemainder_eq

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettRemainder_lt_three_mul_modulus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Fp.barrettRemainder_lt_three_mul_modulus

end Checks.Bls12381FpBarrett
