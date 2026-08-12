import Challenge.Bls12381.ProofSupport.Fp2Source

set_option warningAsError true

namespace Checks.Bls12381Fp2SourceCanonical

open Challenge.Bls12381.ProofSupport

example {a b : Fp2.Repr} (ha : Fp2.Canonical a) (hb : Fp2.Canonical b) :
    Fp2.Canonical (Fp2.addSource a b) := Fp2.canonical_addSource ha hb

example {a b : Fp2.Repr} (ha : Fp2.Canonical a) (hb : Fp2.Canonical b) :
    Fp2.Canonical (Fp2.subSource a b) := Fp2.canonical_subSource ha hb

example {a : Fp2.Repr} (ha : Fp2.Canonical a) :
    Fp2.Canonical (Fp2.negSource a) := Fp2.canonical_negSource ha

example {a b : Fp2.Repr} (ha : Fp2.Canonical a) (hb : Fp2.Canonical b) :
    Fp2.Canonical (Fp2.mulSource a b) := Fp2.canonical_mulSource ha hb

example {a : Fp2.Repr} (ha : Fp2.Canonical a) :
    Fp2.Canonical (Fp2.sqrSource a) := Fp2.canonical_sqrSource ha

example {a : Fp2.Repr} (ha : Fp2.Canonical a) :
    Fp2.Canonical (Fp2.invSource a) := Fp2.canonical_invSource ha

example {a : Fp2.Repr} {s : Fp.Limbs}
    (ha : Fp2.Canonical a) (hs : Fp.Canonical s) :
    Fp2.Canonical (Fp2.mulFpSource a s) := Fp2.canonical_mulFpSource ha hs

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp2.canonical_iff

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_mkRepr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp2.canonical_mkRepr

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.sqrSource_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp2.sqrSource_eq

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_addSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_addSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_subSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_subSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_negSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_negSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_mulSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_mulSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_sqrSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_sqrSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_invSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_invSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_mulFpSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_mulFpSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_mulV0Source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_mulV0Source

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_mulV1Source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_mulV1Source

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_mulRealSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_mulRealSource

/--
info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_mulImaginarySource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp2.canonical_mulImaginarySource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_mulC0Source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_mulC0Source

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_mulC1Source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_mulC1Source

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_sqrRealSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_sqrRealSource

/--
info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_sqrImaginarySource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp2.canonical_sqrImaginarySource

/--
info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_sqrProductSource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp2.canonical_sqrProductSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_sqrC1Source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_sqrC1Source

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_invNormSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_invNormSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_invRealSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_invRealSource

/--
info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_invImaginarySource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp2.canonical_invImaginarySource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_invC0Source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_invC0Source

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_invC1Source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_invC1Source

end Checks.Bls12381Fp2SourceCanonical
