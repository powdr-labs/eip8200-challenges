import Challenge.Bls12381.ProofSupport.Fp2SqrtLawful

set_option warningAsError true

namespace Checks.Bls12381Fp2SqrtLawful

open Challenge.Bls12381.ProofSupport

example {a : LawfulFp2.Carrier} :
    (Fp2.SqrtProgram.run Fp2.lawfulSqrtOps a).exists_ = true ↔
      IsSquare a :=
  Fp2.lawfulSqrtRun_exists_iff

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.norm_isSquare_of_isSquare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Fp2.norm_isSquare_of_isSquare

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.alpha_or_beta_isSquare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.alpha_or_beta_isSquare

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.candidate_nonzero_plus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.candidate_nonzero_plus

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.candidate_nonzero_minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.candidate_nonzero_minus

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.candidate_zero_plus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.candidate_zero_plus

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.beta_root_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.beta_root_ne_zero

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.lawfulSqrtRun_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.lawfulSqrtRun_complete

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.lawfulSqrtRun_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.lawfulSqrtRun_success

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.lawfulSqrtRun_exists_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Fp2.lawfulSqrtRun_exists_iff

end Checks.Bls12381Fp2SqrtLawful
