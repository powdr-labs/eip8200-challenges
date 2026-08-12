import Challenge.Bls12381.ProofSupport.FpAddSub

set_option warningAsError true

namespace Checks.Bls12381FpAddSub

open Challenge.Bls12381.ProofSupport

example {a b : Fp.Limbs} (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.value (Fp.addSource a b) = (Fp.value a + Fp.value b) %
      EvmSemantics.Crypto.Bls12381.p := Fp.value_addSource ha hb

example {a b : Fp.Limbs} (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.value (Fp.subSource a b) =
      (EvmSemantics.Crypto.Bls12381.p + Fp.value a - Fp.value b) %
        EvmSemantics.Crypto.Bls12381.p := Fp.value_subSource ha hb

example {a b : Fp.Limbs} (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.Canonical (Fp.subSource a b) := Fp.canonical_subSource ha hb

example {a b : Fp.Limbs} (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.toField (Fp.subSource a b) = Fp.toField a - Fp.toField b :=
  Fp.toField_subSource ha hb

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    Fp.value (Fp.negSource a) =
      (EvmSemantics.Crypto.Bls12381.p - Fp.value a) %
        EvmSemantics.Crypto.Bls12381.p := Fp.value_negSource ha

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.toWide_subRaw' does not depend on any axioms -/
#guard_msgs in
#print axioms Fp.toWide_subRaw

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.toWide_subRepair' does not depend on any axioms -/
#guard_msgs in
#print axioms Fp.toWide_subRepair

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_subRepair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_subRepair

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.subRepairCondition_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.subRepairCondition_iff

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_subSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_subSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_subSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.canonical_subSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.toField_subSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.toField_subSource

end Checks.Bls12381FpAddSub
