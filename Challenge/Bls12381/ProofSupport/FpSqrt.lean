import Challenge.Bls12381.ProofSupport.FpSqrtConstants
import Challenge.Bls12381.ProofSupport.FpSquare
import Challenge.Bls12381.ProofSupport.FpPredicates
import Challenge.Bls12381.ProofSupport.FpSqrtLawful

set_option warningAsError true

/-! # Source-faithful BLS12-381 base-field square roots -/

namespace Challenge.Bls12381.ProofSupport.Fp

open PrimeField

/-- Exact source call `Fp.sqrt(a) = _modexp(a, P_PLUS_1_DIV_4)`. -/
def sqrtCanonical (a : Limbs) : Limbs :=
  montgomeryPowDecoded a pPlus1Div4Bytes

theorem canonical_sqrtCanonical {a : Limbs} (ha : Canonical a) :
    Canonical (sqrtCanonical a) :=
  canonical_montgomeryPowDecoded ha pPlus1Div4Bytes

/-- The source call refines to the fixed square-root exponent. -/
theorem lawful_sqrtCanonical_pow {a : Limbs} (ha : Canonical a) :
    (value (sqrtCanonical a) : LawfulFp) =
      (value a : LawfulFp) ^
        ((EvmSemantics.Crypto.Bls12381.p + 1) / 4) := by
  rw [sqrtCanonical, lawful_montgomeryPowDecoded ha,
    bytesValue_pPlus1Div4Bytes]

/-- The concrete source exponentiation refines the algebraic square-root
boundary over the certified prime field. -/
theorem sqrtCanonical_refines_lawful {a : Limbs} (ha : Canonical a) :
    (value (sqrtCanonical a) : LawfulFp) = lawfulSqrt (value a : LawfulFp) := by
  rw [lawful_sqrtCanonical_pow ha, lawfulSqrt_eq]

@[simp] theorem lawful_sqrtCanonical_zero {a : Limbs} (ha : Canonical a)
    (hzero : value a = 0) :
    (value (sqrtCanonical a) : LawfulFp) = 0 := by
  rw [lawful_sqrtCanonical_pow ha, hzero]
  norm_num [EvmSemantics.Crypto.Bls12381.p,
    EvmSemantics.Crypto.Bls12381.absU]

/-- Source control flow: zero fast path, square root, square-back, equality. -/
def isSquareCanonical (a : Limbs) : Bool :=
  if isZeroValue a then true
  else
    let root := sqrtCanonical a
    let check := squareCanonical root
    eqCanonicalValue check a

@[simp] theorem isSquareCanonical_zero {a : Limbs} (hzero : value a = 0) :
    isSquareCanonical a = true := by
  simp [isSquareCanonical, isZeroValue, hzero]

theorem lawful_squareCanonical {a : Limbs} (ha : Canonical a) :
    (value (squareCanonical a) : LawfulFp) =
      (value a : LawfulFp) ^ 2 := by
  rw [← finEquiv_toField, toField_squareCanonical ha, map_pow,
    finEquiv_toField]

/-- Square-back verification for every canonical quadratic residue. -/
theorem lawful_square_sqrtCanonical {a : Limbs} (ha : Canonical a)
    (hsquare : IsSquare (value a : LawfulFp)) :
    (value (squareCanonical (sqrtCanonical a)) : LawfulFp) =
      (value a : LawfulFp) := by
  rw [lawful_squareCanonical (canonical_sqrtCanonical ha),
    lawful_sqrtCanonical_pow ha]
  exact lawful_sqrt_pow_square_of_isSquare _ hsquare

/-- Exact canonical-limb square-back result consumed by extension-field square
root algorithms. -/
theorem square_sqrtCanonical {a : Limbs} (ha : Canonical a)
    (hsquare : IsSquare (value a : LawfulFp)) :
    squareCanonical (sqrtCanonical a) = a := by
  apply limbs_ext_of_value_eq
  exact value_eq_of_lawful_eq
    (canonical_squareCanonical (canonical_sqrtCanonical ha)) ha
    (lawful_square_sqrtCanonical ha hsquare)

theorem isSquareCanonical_sound {a : Limbs} (ha : Canonical a)
    (hsquare : isSquareCanonical a = true) :
    IsSquare (value a : LawfulFp) := by
  unfold isSquareCanonical at hsquare
  split at hsquare
  next hzero =>
    have hvalueZero := (isZeroValue_eq_true a).mp hzero
    rw [hvalueZero]
    exact ⟨0, by simp⟩
  next hnonzero =>
    have hvalue := (eqCanonicalValue_eq_true _ _).mp hsquare
    refine ⟨(value (sqrtCanonical a) : LawfulFp), ?_⟩
    have hcast := congrArg (fun n : Nat => (n : LawfulFp)) hvalue
    rw [lawful_squareCanonical (canonical_sqrtCanonical ha)] at hcast
    simpa only [pow_two] using hcast.symm

theorem isSquareCanonical_complete {a : Limbs} (ha : Canonical a)
    (hsquare : IsSquare (value a : LawfulFp)) :
    isSquareCanonical a = true := by
  by_cases hzero : value a = 0
  · exact isSquareCanonical_zero hzero
  · rw [isSquareCanonical, if_neg (by simpa using hzero)]
    apply (eqCanonicalValue_eq_true _ _).2
    exact value_eq_of_lawful_eq
      (canonical_squareCanonical (canonical_sqrtCanonical ha)) ha
      (lawful_square_sqrtCanonical ha hsquare)

theorem isSquareCanonical_iff {a : Limbs} (ha : Canonical a) :
    isSquareCanonical a = true ↔
      IsSquare (value a : LawfulFp) := by
  constructor
  · exact isSquareCanonical_sound ha
  · exact isSquareCanonical_complete ha

end Challenge.Bls12381.ProofSupport.Fp
