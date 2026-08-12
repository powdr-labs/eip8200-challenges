import Challenge.Bls12381.ProofSupport.FpAddSubLawful

set_option warningAsError true

namespace Checks.Bls12381FpAddSubLawful

open Challenge.Bls12381.ProofSupport

example {a b : Fp.Limbs} (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    PrimeField.finEquiv (Fp.toField (Fp.addSource a b)) =
      PrimeField.finEquiv (Fp.toField a) + PrimeField.finEquiv (Fp.toField b) :=
  Fp.toLawful_addSource ha hb

example {a b : Fp.Limbs} (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    PrimeField.finEquiv (Fp.toField (Fp.subSource a b)) =
      PrimeField.finEquiv (Fp.toField a) - PrimeField.finEquiv (Fp.toField b) :=
  Fp.toLawful_subSource ha hb

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    PrimeField.finEquiv (Fp.toField (Fp.negSource a)) =
      -PrimeField.finEquiv (Fp.toField a) :=
  Fp.toLawful_negSource ha

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.toLawful_addSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.toLawful_addSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.toLawful_subSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.toLawful_subSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.toLawful_negSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.toLawful_negSource

end Checks.Bls12381FpAddSubLawful
