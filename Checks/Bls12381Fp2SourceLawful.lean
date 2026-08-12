import Challenge.Bls12381.ProofSupport.Fp2SourceLawful

set_option warningAsError true

namespace Checks.Bls12381Fp2SourceLawful

open Challenge.Bls12381.ProofSupport

example {a b : Fp2.Repr} (ha : Fp2.Canonical a) (hb : Fp2.Canonical b) :
    Fp2.toField (Fp2.addSource a b) = Fp2.toField a + Fp2.toField b :=
  Fp2.toField_addSource ha hb

example {a b : Fp2.Repr} (ha : Fp2.Canonical a) (hb : Fp2.Canonical b) :
    Fp2.toField (Fp2.subSource a b) = Fp2.toField a - Fp2.toField b :=
  Fp2.toField_subSource ha hb

example {a : Fp2.Repr} (ha : Fp2.Canonical a) :
    Fp2.toField (Fp2.negSource a) = -Fp2.toField a :=
  Fp2.toField_negSource ha

example {a : Fp2.Repr} {s : Fp.Limbs}
    (ha : Fp2.Canonical a) (hs : Fp.Canonical s) :
    Fp2.toField (Fp2.mulFpSource a s) =
      { c0 := Fp.toField a.c0 * Fp.toField s
        c1 := Fp.toField a.c1 * Fp.toField s } :=
  Fp2.toField_mulFpSource ha hs

example {a b : Fp2.Repr} (ha : Fp2.Canonical a) (hb : Fp2.Canonical b) :
    Fp2.toLawful (Fp2.addSource a b) = Fp2.toLawful a + Fp2.toLawful b :=
  Fp2.toLawful_addSource ha hb

example {a b : Fp2.Repr} (ha : Fp2.Canonical a) (hb : Fp2.Canonical b) :
    Fp2.toLawful (Fp2.subSource a b) = Fp2.toLawful a - Fp2.toLawful b :=
  Fp2.toLawful_subSource ha hb

example {a : Fp2.Repr} (ha : Fp2.Canonical a) :
    Fp2.toLawful (Fp2.negSource a) = -Fp2.toLawful a :=
  Fp2.toLawful_negSource ha

example {a : Fp2.Repr} {s : Fp.Limbs}
    (ha : Fp2.Canonical a) (hs : Fp.Canonical s) :
    Fp2.toLawful (Fp2.mulFpSource a s) =
      algebraMap LawfulFp2.Base LawfulFp2.Carrier
        (PrimeField.finEquiv (Fp.toField s)) * Fp2.toLawful a :=
  Fp2.toLawful_mulFpSource ha hs

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toField_mkRepr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp2.toField_mkRepr

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toLawful_mkRepr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toLawful_mkRepr

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toField_addSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toField_addSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toField_subSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toField_subSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toField_negSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toField_negSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toField_mulFpSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toField_mulFpSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toLawful_addSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toLawful_addSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toLawful_subSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toLawful_subSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toLawful_negSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toLawful_negSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.toLawful_mulFpSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.toLawful_mulFpSource

end Checks.Bls12381Fp2SourceLawful
