import Challenge.Bls12381.ProofSupport.FpPredicates

set_option warningAsError true

namespace Checks.Bls12381FpPredicates

open Challenge.Bls12381.ProofSupport

example (a : Fp.Limbs) : Fp.isZeroValue a = true ↔ Fp.value a = 0 :=
  Fp.isZeroValue_eq_true a

example (a b : Fp.Limbs) :
    Fp.eqCanonicalValue a b = true ↔ Fp.value a = Fp.value b :=
  Fp.eqCanonicalValue_eq_true a b

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.isZeroValue_eq_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp.isZeroValue_eq_true

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.eqCanonicalValue_eq_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp.eqCanonicalValue_eq_true

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.limbs_ext_of_value_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.limbs_ext_of_value_eq

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_eq_of_lawful_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_eq_of_lawful_eq

end Checks.Bls12381FpPredicates
