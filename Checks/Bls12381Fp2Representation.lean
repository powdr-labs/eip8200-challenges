import Challenge.Bls12381.ProofSupport.Fp2Representation

set_option warningAsError true

namespace Checks.Bls12381Fp2Representation

open Challenge.Bls12381.ProofSupport

example :
    Challenge.Bls12381.ProofSupport.Fp2.toLawful
        Challenge.Bls12381.ProofSupport.Fp2.zero = 0 :=
  Challenge.Bls12381.ProofSupport.Fp2.toLawful_zero_repr

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toLawful_zero_repr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toLawful_zero_repr

end Checks.Bls12381Fp2Representation
