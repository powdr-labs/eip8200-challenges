import Challenge.Bls12381.ProofSupport.Fp2SourceLawful

set_option warningAsError true

namespace Checks.Bls12381Fp2SourceMul

open Challenge.Bls12381.ProofSupport

example {a b : Fp2.Repr} (ha : Fp2.Canonical a) (hb : Fp2.Canonical b) :
    Fp2.toField (Fp2.mulSource a b) = Fp2.toField a * Fp2.toField b :=
  Fp2.toField_mulSource ha hb

example {a b : Fp2.Repr} (ha : Fp2.Canonical a) (hb : Fp2.Canonical b) :
    Fp2.Canonical (Fp2.mulSource a b) ∧
      Fp2.toField (Fp2.mulSource a b) = Fp2.toField a * Fp2.toField b :=
  Fp2.mulSource_spec ha hb

example {a : Fp2.Repr} (ha : Fp2.Canonical a) :
    Fp2.toField (Fp2.sqrSource a) = _root_.Fp2.square (Fp2.toField a) :=
  Fp2.toField_sqrSource ha

example {a b : Fp2.Repr} (ha : Fp2.Canonical a) (hb : Fp2.Canonical b) :
    Fp2.toLawful (Fp2.mulSource a b) = Fp2.toLawful a * Fp2.toLawful b :=
  Fp2.toLawful_mulSource ha hb

example {a : Fp2.Repr} (ha : Fp2.Canonical a) :
    Fp2.toLawful (Fp2.sqrSource a) = Fp2.toLawful a * Fp2.toLawful a :=
  Fp2.toLawful_sqrSource ha

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toField_mulC0Source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toField_mulC0Source

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toField_mulC1Source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toField_mulC1Source

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toField_mulSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toField_mulSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.mulSource_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.mulSource_spec

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toField_sqrRealSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toField_sqrRealSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toField_sqrC1Source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toField_sqrC1Source

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toField_sqrSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toField_sqrSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toLawful_mulSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toLawful_mulSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toLawful_sqrSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toLawful_sqrSource

end Checks.Bls12381Fp2SourceMul
