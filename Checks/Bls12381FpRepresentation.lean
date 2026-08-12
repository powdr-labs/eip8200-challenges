import Challenge.Bls12381.ProofSupport.FpRepresentation

set_option warningAsError true

namespace Checks.Bls12381FpRepresentation

open Challenge.Bls12381.ProofSupport

example (a : Fp.Limbs)
    (hvalue : Fp.value a < EvmSemantics.Crypto.Bls12381.p) :
    Fp.Canonical a := Fp.canonical_of_value_lt a hvalue

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_of_value_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.canonical_of_value_lt

end Checks.Bls12381FpRepresentation
