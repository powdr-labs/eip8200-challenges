import Challenge.Bls12381.ProofSupport.FpInvConstants

set_option warningAsError true

namespace Checks.Bls12381FpInvConstants

open Challenge.Bls12381.ProofSupport

example : Fp.pMinus2Bytes = [
    0x1a, 0x01, 0x11, 0xea, 0x39, 0x7f, 0xe6, 0x9a,
    0x4b, 0x1b, 0xa7, 0xb6, 0x43, 0x4b, 0xac, 0xd7,
    0x64, 0x77, 0x4b, 0x84, 0xf3, 0x85, 0x12, 0xbf,
    0x67, 0x30, 0xd2, 0xa0, 0xf6, 0xb0, 0xf6, 0x24,
    0x1e, 0xab, 0xff, 0xfe, 0xb1, 0x53, 0xff, 0xff,
    0xb9, 0xfe, 0xff, 0xff, 0xff, 0xff, 0xaa, 0xa9] :=
  rfl

example : Fp.pMinus2Bytes.length = 48 := Fp.length_pMinus2Bytes

example : Fp.bytesValue Fp.pMinus2Bytes =
    EvmSemantics.Crypto.Bls12381.p - 2 :=
  Fp.bytesValue_pMinus2Bytes

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.length_pMinus2Bytes' does not depend on any axioms -/
#guard_msgs in
#print axioms Fp.length_pMinus2Bytes

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.bytesValue_pMinus2Bytes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.bytesValue_pMinus2Bytes

end Checks.Bls12381FpInvConstants
