import Challenge.Bls12381.ProofSupport.FpRepresentation
import Challenge.Bls12381.ProofSupport.PrimeField

set_option warningAsError true

/-! # Decoded canonical base-field predicates -/

namespace Challenge.Bls12381.ProofSupport.Fp

open PrimeField

@[simp] theorem finEquiv_toField (a : Limbs) :
    PrimeField.finEquiv (toField a) = (value a : LawfulFp) := by
  rfl

/-- Canonical-value zero test. The byte-level equivalence to
`LimbMath.isZeroBytes` belongs to codec refinement. -/
def isZeroValue (a : Limbs) : Bool := value a == 0

/-- Canonical-value equality. Its equivalence to equality of canonical
48-byte encodings belongs to codec refinement. -/
def eqCanonicalValue (a b : Limbs) : Bool := value a == value b

@[simp] theorem isZeroValue_eq_true (a : Limbs) :
    isZeroValue a = true ↔ value a = 0 := by
  simp [isZeroValue]

@[simp] theorem eqCanonicalValue_eq_true (a b : Limbs) :
    eqCanonicalValue a b = true ↔ value a = value b := by
  simp [eqCanonicalValue]

/-- The natural reconstruction uniquely determines its two EVM words. -/
theorem limbs_ext_of_value_eq {a b : Limbs} (hvalue : value a = value b) :
    a = b := by
  have hloA := a.lo.val.isLt
  have hloB := b.lo.val.isLt
  change a.lo.toNat < Challenge.EvmProof.Limbs.radix at hloA
  change b.lo.toNat < Challenge.EvmProof.Limbs.radix at hloB
  have hhigh := congrArg
    (fun n => n / Challenge.EvmProof.Limbs.radix) hvalue
  unfold value at hhigh
  rw [Nat.add_mul_div_left _ _ Challenge.EvmProof.Limbs.radix_pos,
    Nat.add_mul_div_left _ _ Challenge.EvmProof.Limbs.radix_pos] at hhigh
  rw [Nat.div_eq_of_lt hloA, Nat.div_eq_of_lt hloB] at hhigh
  simp only [Nat.zero_add] at hhigh
  have hlow : a.lo.toNat = b.lo.toNat := by
    unfold value at hvalue
    rw [hhigh] at hvalue
    omega
  exact congrArg₂ Limbs.mk
    (Challenge.EvmProof.Word.word_ext hhigh)
    (Challenge.EvmProof.Word.word_ext hlow)

/-- Lawful-field equality is injective on canonical decoded values. -/
theorem value_eq_of_lawful_eq {a b : Limbs} (ha : Canonical a)
    (hb : Canonical b)
    (hvalue : (value a : LawfulFp) = (value b : LawfulFp)) :
    value a = value b := by
  have hmod : Nat.ModEq EvmSemantics.Crypto.Bls12381.p (value a) (value b) :=
    (ZMod.natCast_eq_natCast_iff _ _
      EvmSemantics.Crypto.Bls12381.p).mp hvalue
  exact hmod.eq_of_lt_of_lt ha.2 hb.2

end Challenge.Bls12381.ProofSupport.Fp
