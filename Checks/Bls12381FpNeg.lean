import Challenge.Bls12381.ProofSupport.FpAddSub

set_option warningAsError true

namespace Checks.Bls12381FpNeg

open Challenge.Bls12381.ProofSupport

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    Fp.value (Fp.negSource a) =
      (EvmSemantics.Crypto.Bls12381.p - Fp.value a) %
        EvmSemantics.Crypto.Bls12381.p := Fp.value_negSource ha

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    Fp.Canonical (Fp.negSource a) := Fp.canonical_negSource ha

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    Fp.toField (Fp.negSource a) = -Fp.toField a := Fp.toField_negSource ha

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.toWide_negNonzero' does not depend on any axioms -/
#guard_msgs in
#print axioms Fp.toWide_negNonzero

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_negSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_negSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_negSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.canonical_negSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.toField_negSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.toField_negSource

end Checks.Bls12381FpNeg
