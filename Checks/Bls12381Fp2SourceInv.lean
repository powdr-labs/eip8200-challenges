import Challenge.Bls12381.ProofSupport.Fp2SourceLawful

set_option warningAsError true

namespace Checks.Bls12381Fp2SourceInv

open Challenge.Bls12381.ProofSupport

example {a : Fp2.Repr} (ha : Fp2.Canonical a) :
    PrimeField.finEquiv (Fp.toField (Fp2.invNormSource a)) =
      QuadraticAlgebra.norm (Fp2.toLawful a) :=
  Fp2.toLawful_invNormSource ha

example {a : Fp2.Repr} (ha : Fp2.Canonical a) :
    Fp2.toLawful (Fp2.invSource a) = (Fp2.toLawful a)⁻¹ :=
  Fp2.toLawful_invSource ha

example {a : Fp2.Repr} (ha : Fp2.Canonical a)
    (hzero : Fp2.toLawful a = 0) : Fp2.toLawful (Fp2.invSource a) = 0 :=
  Fp2.toLawful_invSource_zero ha hzero

example {a : Fp2.Repr} (ha : Fp2.Canonical a)
    (hne : Fp2.toLawful a ≠ 0) :
    Fp2.toLawful a * Fp2.toLawful (Fp2.invSource a) = 1 :=
  Fp2.toLawful_mul_invSource ha hne

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toLawful_invNormSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toLawful_invNormSource

/--
info: 'Challenge.Bls12381.ProofSupport.Fp2.toLawful_invNormInvSource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp2.toLawful_invNormInvSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toLawful_invC0Source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toLawful_invC0Source

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toLawful_invC1Source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toLawful_invC1Source

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toLawful_invSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toLawful_invSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toLawful_invSource_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toLawful_invSource_zero

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toLawful_mul_invSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toLawful_mul_invSource

end Checks.Bls12381Fp2SourceInv
