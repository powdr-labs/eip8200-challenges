import Challenge.Bls12381.ProofSupport.FpBarrettSubtract

set_option warningAsError true

namespace Checks.Bls12381FpBarrettSubtract

open Challenge.Bls12381.ProofSupport
open EvmSemantics

example (product : Fp.SchoolbookProduct) :
    Fp.barrettRemainder product =
      Challenge.EvmProof.Limbs.subWide256
        (Fp.productLowWords product) (Fp.barrettMultipleLow product) := rfl

example (product : Fp.SchoolbookProduct) :
    (Fp.barrettRemainder product).hi =
      product.r1 - (Fp.barrettMultipleLow product).hi -
        UInt256.lt product.r0 (Fp.barrettMultipleLow product).lo := rfl

example (product : Fp.SchoolbookProduct) :
    (Fp.barrettMultipleLow product).value =
      ((Fp.barrettQuotient product).value *
        EvmSemantics.Crypto.Bls12381.p) %
          Challenge.EvmProof.Limbs.radix ^ 2 :=
  Fp.value_barrettMultipleLow product

example (product : Fp.SchoolbookProduct)
    (hproduct : product.value < EvmSemantics.Crypto.Bls12381.p ^ 2) :
    (Fp.barrettRemainder product).value =
      product.value -
        (Fp.barrettQuotient product).value *
          EvmSemantics.Crypto.Bls12381.p :=
  Fp.value_barrettRemainder product hproduct

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_barrettMultipleLow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_barrettMultipleLow

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_productLowWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_productLowWords

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_barrettRemainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_barrettRemainder

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.quotientWords_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.quotientWords_value

end Checks.Bls12381FpBarrettSubtract
