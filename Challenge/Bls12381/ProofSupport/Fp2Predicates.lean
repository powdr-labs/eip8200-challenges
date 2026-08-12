import Challenge.Bls12381.ProofSupport.Fp2Representation
import Challenge.Bls12381.ProofSupport.FpParity
import Challenge.Bls12381.ProofSupport.FpPredicates

set_option warningAsError true

/-! # Source-faithful decoded Fp2 predicates -/

namespace Challenge.Bls12381.ProofSupport.Fp2

/-- Exact component order of `Fp2.isZero`. -/
def isZeroSource (a : Repr) : Bool :=
  Fp.isZeroValue a.c0 && Fp.isZeroValue a.c1

/-- Exact component order of `Fp2.eq`. At this decoded canonical boundary,
component-value equality represents equality of the canonical 48-byte strings;
the byte/hash bridge belongs to codec refinement. -/
def eqSource (a b : Repr) : Bool :=
  Fp.eqCanonicalValue a.c0 b.c0 && Fp.eqCanonicalValue a.c1 b.c1

/-- RFC 9380 `sgn0` source formula `sign0 | (zero0 & sign1)`. -/
def sgn0Source (a : Repr) : Nat :=
  let sign0 := Fp.sgn0Value a.c0
  let zero0 := if Fp.isZeroValue a.c0 then 1 else 0
  let sign1 := Fp.sgn0Value a.c1
  Nat.lor sign0 (Nat.land zero0 sign1)

theorem sgn0Source_eq (a : Repr) :
    sgn0Source a =
      if Fp.value a.c0 = 0 then Fp.value a.c1 % 2
      else Fp.value a.c0 % 2 := by
  by_cases hzero : Fp.value a.c0 = 0
  · simp [sgn0Source, Fp.sgn0Value, Fp.isZeroValue, hzero]
  · simp [sgn0Source, Fp.sgn0Value, Fp.isZeroValue, hzero]

theorem isZeroSource_eq_true (a : Repr) :
    isZeroSource a = true ↔ Fp.value a.c0 = 0 ∧ Fp.value a.c1 = 0 := by
  simp [isZeroSource]

theorem eqSource_eq_true (a b : Repr) :
    eqSource a b = true ↔
      Fp.value a.c0 = Fp.value b.c0 ∧
        Fp.value a.c1 = Fp.value b.c1 := by
  simp [eqSource]

theorem eq_of_eqSource_true {a b : Repr} (heq : eqSource a b = true) :
    a = b := by
  rw [eqSource_eq_true] at heq
  cases a
  cases b
  rw [Repr.mk.injEq]
  exact ⟨Fp.limbs_ext_of_value_eq heq.1,
    Fp.limbs_ext_of_value_eq heq.2⟩

theorem eq_zero_of_isZeroSource_true {a : Repr}
    (hzero : isZeroSource a = true) : a = zero := by
  rw [isZeroSource_eq_true] at hzero
  cases a
  rw [Repr.mk.injEq]
  exact ⟨Fp.limbs_ext_of_value_eq (by simpa [zero] using hzero.1),
    Fp.limbs_ext_of_value_eq (by simpa [zero] using hzero.2)⟩

theorem isZeroSource_iff {a : Repr} (ha : Canonical a) :
    isZeroSource a = true ↔ toLawful a = 0 := by
  rw [isZeroSource_eq_true]
  constructor
  · rintro ⟨hc0, hc1⟩
    apply QuadraticAlgebra.ext
    · change (Fp.value a.c0 : PrimeField.LawfulFp) = 0
      rw [hc0]
      norm_num
    · change (Fp.value a.c1 : PrimeField.LawfulFp) = 0
      rw [hc1]
      norm_num
  · intro hzero
    have hre := congrArg QuadraticAlgebra.re hzero
    have him := congrArg QuadraticAlgebra.im hzero
    change (Fp.value a.c0 : PrimeField.LawfulFp) = 0 at hre
    change (Fp.value a.c1 : PrimeField.LawfulFp) = 0 at him
    constructor
    · exact Fp.value_eq_of_lawful_eq ha.c0.proof (Fp.canonical_normalize 0)
        (by simpa using hre)
    · exact Fp.value_eq_of_lawful_eq ha.c1.proof (Fp.canonical_normalize 0)
        (by simpa using him)

theorem eqSource_iff {a b : Repr} (ha : Canonical a) (hb : Canonical b) :
    eqSource a b = true ↔ toLawful a = toLawful b := by
  rw [eqSource_eq_true]
  constructor
  · rintro ⟨hc0, hc1⟩
    apply QuadraticAlgebra.ext
    · change (Fp.value a.c0 : PrimeField.LawfulFp) =
        (Fp.value b.c0 : PrimeField.LawfulFp)
      rw [hc0]
    · change (Fp.value a.c1 : PrimeField.LawfulFp) =
        (Fp.value b.c1 : PrimeField.LawfulFp)
      rw [hc1]
  · intro heq
    have hre := congrArg QuadraticAlgebra.re heq
    have him := congrArg QuadraticAlgebra.im heq
    change (Fp.value a.c0 : PrimeField.LawfulFp) =
      (Fp.value b.c0 : PrimeField.LawfulFp) at hre
    change (Fp.value a.c1 : PrimeField.LawfulFp) =
      (Fp.value b.c1 : PrimeField.LawfulFp) at him
    exact ⟨Fp.value_eq_of_lawful_eq ha.c0.proof hb.c0.proof hre,
      Fp.value_eq_of_lawful_eq ha.c1.proof hb.c1.proof him⟩

theorem eq_of_lawful_eq {a b : Repr} (ha : Canonical a) (hb : Canonical b)
    (heq : toLawful a = toLawful b) : a = b :=
  eq_of_eqSource_true ((eqSource_iff ha hb).2 heq)

end Challenge.Bls12381.ProofSupport.Fp2
