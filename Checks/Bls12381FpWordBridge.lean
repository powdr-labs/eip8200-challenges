import Challenge.Bls12381.ProofSupport.FpWordBridge

set_option warningAsError true

namespace Checks.Bls12381FpWordBridge

open Challenge.Bls12381.ProofSupport

example (a : Fp.Limbs) : (Fp.toWide a).value = Fp.value a :=
  Fp.toWide_value a

example (words : Challenge.EvmProof.Limbs.WideProduct) :
    Fp.value (Fp.ofWide words) = words.value := Fp.value_ofWide words

example : Fp.modulusWide.value = EvmSemantics.Crypto.Bls12381.p :=
  Fp.modulusWide_value

example (a : Fp.Limbs) : Fp.ofWide (Fp.toWide a) = a := Fp.ofWide_toWide a

example (words : Challenge.EvmProof.Limbs.WideProduct) :
    Fp.toWide (Fp.ofWide words) = words := Fp.toWide_ofWide words

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.toWide_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.toWide_value

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_ofWide' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.value_ofWide

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.modulusWide_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.modulusWide_value

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.ofWide_toWide' does not depend on any axioms -/
#guard_msgs in
#print axioms Fp.ofWide_toWide

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.toWide_ofWide' does not depend on any axioms -/
#guard_msgs in
#print axioms Fp.toWide_ofWide

end Checks.Bls12381FpWordBridge
