import Challenge.Bls12381.ProofSupport.FpSqrtConstants

set_option warningAsError true

namespace Checks.Bls12381FpSqrtConstants

open Challenge.Bls12381.ProofSupport

example : Fp.pPlus1Div4Bytes.length = 48 :=
  Fp.length_pPlus1Div4Bytes

example : Fp.bytesValue Fp.pPlus1Div4Bytes =
    (EvmSemantics.Crypto.Bls12381.p + 1) / 4 :=
  Fp.bytesValue_pPlus1Div4Bytes

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.length_pPlus1Div4Bytes' does not depend on any axioms -/
#guard_msgs in
#print axioms Fp.length_pPlus1Div4Bytes

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.bytesValue_pPlus1Div4Bytes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.bytesValue_pPlus1Div4Bytes

end Checks.Bls12381FpSqrtConstants
