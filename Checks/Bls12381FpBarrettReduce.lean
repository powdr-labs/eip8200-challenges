import Challenge.Bls12381.ProofSupport.FpBarrettReduce

set_option warningAsError true

namespace Checks.Bls12381FpBarrettReduce

open Challenge.Bls12381.ProofSupport
open EvmSemantics

example (remainder : Challenge.EvmProof.Limbs.WideProduct) :
    (Fp.barrettSubModulus remainder).hi =
      remainder.hi - Fp.modulusHi - UInt256.gt Fp.modulusLo remainder.lo := rfl

example (remainder : Challenge.EvmProof.Limbs.WideProduct) :
    Fp.barrettSubModulus remainder =
      Challenge.EvmProof.Limbs.subWide256 remainder Fp.modulusWide :=
  Fp.barrettSubModulus_eq_subWide256 remainder

example (remainder : Challenge.EvmProof.Limbs.WideProduct) :
    (Fp.barrettCorrectOnce remainder).value =
      if EvmSemantics.Crypto.Bls12381.p ≤ remainder.value then
        remainder.value - EvmSemantics.Crypto.Bls12381.p
      else remainder.value :=
  Fp.value_barrettCorrectOnce remainder

example (product : Fp.SchoolbookProduct)
    (hproduct : product.value < EvmSemantics.Crypto.Bls12381.p ^ 2) :
    (Fp.barrettReduce product).value =
      product.value % EvmSemantics.Crypto.Bls12381.p :=
  Fp.value_barrettReduce product hproduct

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_barrettCorrectOnce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_barrettCorrectOnce

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.twoConditionalSubtractions_eq_mod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Fp.twoConditionalSubtractions_eq_mod

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_barrettReduce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_barrettReduce

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettSubModulus_eq_subWide256' does not depend on any axioms -/
#guard_msgs in
#print axioms Fp.barrettSubModulus_eq_subWide256

end Checks.Bls12381FpBarrettReduce
