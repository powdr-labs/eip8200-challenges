import Challenge.Bls12381.ProofSupport.Fp2Predicates

set_option warningAsError true

namespace Checks.Bls12381Fp2Predicates

open Challenge.Bls12381.ProofSupport

example (a : Fp.Limbs) : Fp.sgn0Value a = Fp.value a % 2 := rfl

example (a : Fp2.Repr) :
    Fp2.isZeroSource a =
      (Fp.isZeroValue a.c0 && Fp.isZeroValue a.c1) := rfl

example (a b : Fp2.Repr) :
    Fp2.eqSource a b =
      (Fp.eqCanonicalValue a.c0 b.c0 &&
        Fp.eqCanonicalValue a.c1 b.c1) := rfl

example (a : Fp2.Repr) :
    Fp2.sgn0Source a =
      Nat.lor (Fp.sgn0Value a.c0)
        (Nat.land (if Fp.isZeroValue a.c0 then 1 else 0)
          (Fp.sgn0Value a.c1)) := rfl

example (a : Fp2.Repr) :
    Fp2.sgn0Source a =
      if Fp.value a.c0 = 0 then Fp.value a.c1 % 2
      else Fp.value a.c0 % 2 :=
  Fp2.sgn0Source_eq a

example (a : Fp2.Repr) (ha : Fp2.Canonical a) :
    Fp2.isZeroSource a = true ↔ Fp2.toLawful a = 0 :=
  Fp2.isZeroSource_iff ha

example (a b : Fp2.Repr) (ha : Fp2.Canonical a)
    (hb : Fp2.Canonical b) :
    Fp2.eqSource a b = true ↔ Fp2.toLawful a = Fp2.toLawful b :=
  Fp2.eqSource_iff ha hb

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.sgn0Value_lt_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp.sgn0Value_lt_two

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.sgn0Source_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.sgn0Source_eq

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.isZeroSource_eq_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.isZeroSource_eq_true

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.eqSource_eq_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.eqSource_eq_true

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.eq_of_eqSource_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.eq_of_eqSource_true

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.eq_zero_of_isZeroSource_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Fp2.eq_zero_of_isZeroSource_true

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.isZeroSource_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.isZeroSource_iff

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.eqSource_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.eqSource_iff

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.eq_of_lawful_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.eq_of_lawful_eq

end Checks.Bls12381Fp2Predicates
