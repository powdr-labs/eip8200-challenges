import Challenge.Bls12381.ProofSupport.Fp2SqrtConstants

set_option warningAsError true

namespace Checks.Bls12381Fp2SqrtConstants

open Challenge.Bls12381.ProofSupport

example : Fp2.invTwoBytes.length = 48 := Fp2.length_invTwoBytes

example : Fp.bytesValue Fp2.invTwoBytes =
    (EvmSemantics.Crypto.Bls12381.p + 1) / 2 :=
  Fp2.bytesValue_invTwoBytes

example : Fp.value Fp2.invTwo =
    (EvmSemantics.Crypto.Bls12381.p + 1) / 2 :=
  Fp2.value_invTwo

example : Fp.Canonical Fp2.invTwo := Fp2.canonical_invTwo

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.length_invTwoBytes' does not depend on any axioms -/
#guard_msgs in
#print axioms Fp2.length_invTwoBytes

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.bytesValue_invTwoBytes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp2.bytesValue_invTwoBytes

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.value_invTwo' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp2.value_invTwo

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_invTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_invTwo

end Checks.Bls12381Fp2SqrtConstants
