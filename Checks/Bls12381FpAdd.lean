import Challenge.Bls12381.ProofSupport.FpAddSub

set_option warningAsError true

namespace Checks.Bls12381FpAdd

open Challenge.Bls12381.ProofSupport

example {a b : Fp.Limbs} (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.value (Fp.addSource a b) = (Fp.value a + Fp.value b) %
      EvmSemantics.Crypto.Bls12381.p := Fp.value_addSource ha hb

example {a b : Fp.Limbs} (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.Canonical (Fp.addSource a b) := Fp.canonical_addSource ha hb

example {a b : Fp.Limbs} (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.toField (Fp.addSource a b) = Fp.toField a + Fp.toField b :=
  Fp.toField_addSource ha hb

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_addRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_addRaw

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection_eq_wideGeWord' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.addNeedsCorrection_eq_wideGeWord

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.toWide_addCorrect' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp.toWide_addCorrect

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_addSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_addSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_addSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.canonical_addSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.toField_addSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.toField_addSource

end Checks.Bls12381FpAdd
