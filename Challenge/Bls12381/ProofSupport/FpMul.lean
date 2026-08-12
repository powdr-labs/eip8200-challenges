import Challenge.Bls12381.ProofSupport.FpBarrettReduce
import Challenge.Bls12381.ProofSupport.FpRepresentation
import Challenge.Bls12381.ProofSupport.FpWordBridge

set_option warningAsError true

/-!
# BLS12-381 canonical multiplication

This module exposes the complete source-faithful multiplication boundary:
three-word schoolbook multiplication, the fixed Barrett quotient, exact
low-word subtraction, and two corrective modulus subtractions.
-/

namespace Challenge.Bls12381.ProofSupport.Fp

/-- Source-faithful canonical multiplication.  The implementation contains
only word operations and the fixed Barrett schedule; it does not call `% p`,
`normalize`, or semantic field multiplication. -/
def mulCanonical (a b : Limbs) : Limbs :=
  ofWide (barrettReduce (schoolbookProduct a b))

/-- The concrete word-level implementation reconstructs multiplication modulo
the BLS base-field modulus. -/
theorem value_mulCanonical {a b : Limbs} (ha : Canonical a) (hb : Canonical b) :
    value (mulCanonical a b) =
      (value a * value b) % EvmSemantics.Crypto.Bls12381.p := by
  let product := schoolbookProduct a b
  have hproductValue : product.value = value a * value b :=
    value_schoolbookProduct ha hb
  have hproduct : product.value < EvmSemantics.Crypto.Bls12381.p ^ 2 := by
    rw [hproductValue]
    simpa [pow_two] using Nat.mul_lt_mul_of_lt_of_lt ha.2 hb.2
  unfold mulCanonical
  rw [value_ofWide, value_barrettReduce product hproduct, hproductValue]

/-- The source-level multiplication result is a canonical 48-byte field
element. -/
theorem canonical_mulCanonical {a b : Limbs}
    (ha : Canonical a) (hb : Canonical b) :
    Canonical (mulCanonical a b) := by
  have hvalue : value (mulCanonical a b) <
      EvmSemantics.Crypto.Bls12381.p := by
    rw [value_mulCanonical ha hb]
    exact Nat.mod_lt _ (by
      norm_num [EvmSemantics.Crypto.Bls12381.p,
        EvmSemantics.Crypto.Bls12381.absU])
  exact canonical_of_value_lt _ hvalue

/-- The concrete canonical multiplication refines multiplication in the pinned
`Fin p` carrier. -/
theorem refines_mulCanonical {a b : Limbs}
    (ha : Canonical a) (hb : Canonical b) :
  Refines (mulCanonical a b) (toField a * toField b) := by
  apply Fin.ext
  simp [toField, value_mulCanonical ha hb, Fin.mul_def, Nat.mul_mod]

@[simp] theorem toField_mulCanonical {a b : Limbs}
    (ha : Canonical a) (hb : Canonical b) :
    toField (mulCanonical a b) = toField a * toField b := by
  simpa only [Refines] using refines_mulCanonical ha hb

/-- Consumer contract for source-faithful multiplication. Callers receive the
canonical representation invariant and mathematical field meaning together,
without reopening the word-level multiplication and Barrett schedule. -/
theorem mulCanonical_spec {a b : Limbs}
    (ha : Canonical a) (hb : Canonical b) :
    Canonical (mulCanonical a b) ∧
      toField (mulCanonical a b) = toField a * toField b :=
  ⟨canonical_mulCanonical ha hb, toField_mulCanonical ha hb⟩

end Challenge.Bls12381.ProofSupport.Fp
