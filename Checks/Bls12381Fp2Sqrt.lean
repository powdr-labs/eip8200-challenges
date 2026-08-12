import Challenge.Bls12381.ProofSupport.Fp2Sqrt

set_option warningAsError true

namespace Checks.Bls12381Fp2Sqrt

open Challenge.Bls12381.ProofSupport

example (a : Fp2.Repr) :
    Fp2.sqrtSource a =
      Fp2.SqrtProgram.run Fp2.sqrtSourceOps a := rfl

example {a : Fp2.Repr} (ha : Fp2.Canonical a) :
    Fp2.Canonical (Fp2.sqrtSource a).root :=
  Fp2.canonical_sqrtSource ha

example {a : Fp2.Repr} (ha : Fp2.Canonical a)
    (hsuccess : (Fp2.sqrtSource a).exists_ = true) :
    Fp2.sqrSource (Fp2.sqrtSource a).root = a :=
  Fp2.sqrtSource_success ha hsuccess

example {a : Fp2.Repr} (ha : Fp2.Canonical a) :
    (Fp2.sqrtSource a).exists_ = true ↔
      IsSquare (Fp2.toLawful a) :=
  Fp2.sqrtSource_exists_iff ha

example : (Fp2.sqrtSource Fp2.negativeOne).exists_ = true :=
  Fp2.sqrtSource_negativeOne_success

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_sqrtSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_sqrtSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.sqrtSource_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.sqrtSource_success

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.sqrSource_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.sqrSource_zero

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.sqrtSource_exists_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.sqrtSource_exists_iff

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_negativeOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_negativeOne

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toLawful_negativeOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toLawful_negativeOne

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.sqrtSource_negativeOne_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Fp2.sqrtSource_negativeOne_success

end Checks.Bls12381Fp2Sqrt
