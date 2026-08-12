import Challenge.Bls12381.ProofSupport.Fp2

set_option warningAsError true

/-! # Canonical decoded representation of an Fp2 element -/

namespace Challenge.Bls12381.ProofSupport.Fp2

/-- Opaque evidence that one decoded component is canonical.  The wrapper
prevents kernel weak-head normalization from expanding a nested executable
Fp call graph merely to discover that `Fp.Canonical` is a proposition. -/
structure ComponentCanonical (a : Fp.Limbs) : Prop where
  proof : Fp.Canonical a

/-- Both decoded 48-byte components are canonical BLS base-field values. -/
structure Canonical (a : Repr) : Prop where
  c0 : ComponentCanonical a.c0
  c1 : ComponentCanonical a.c1

/-- Construct a decoded pair without exposing either component computation. -/
def mkRepr (c0 c1 : Fp.Limbs) : Repr := { c0, c1 }

theorem canonical_mkRepr {c0 c1 : Fp.Limbs}
    (hc0 : ComponentCanonical c0) (hc1 : ComponentCanonical c1) :
    Canonical (mkRepr c0 c1) :=
  ⟨hc0, hc1⟩

@[simp] theorem toField_mkRepr (c0 c1 : Fp.Limbs) :
    toField (mkRepr c0 c1) = { c0 := Fp.toField c0, c1 := Fp.toField c1 } := rfl

@[simp] theorem toLawful_mkRepr (c0 c1 : Fp.Limbs) :
    toLawful (mkRepr c0 c1) =
      ⟨PrimeField.finEquiv (Fp.toField c0),
        PrimeField.finEquiv (Fp.toField c1)⟩ := rfl

@[simp] theorem toLawful_zero_repr : toLawful zero = 0 := by
  unfold toLawful
  rw [toField_zero]
  rfl

theorem canonical_iff (a : Repr) :
    Canonical a ↔ Fp.Canonical a.c0 ∧ Fp.Canonical a.c1 := by
  constructor
  · intro ha
    exact ⟨ha.c0.proof, ha.c1.proof⟩
  · rintro ⟨hc0, hc1⟩
    exact ⟨⟨hc0⟩, ⟨hc1⟩⟩

end Challenge.Bls12381.ProofSupport.Fp2
