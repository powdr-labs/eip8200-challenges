import Challenge.Bls12381.ProofSupport.Fp2SqrtDefs
import Challenge.Bls12381.ProofSupport.Fp2SqrtLawfulOps
import Challenge.Bls12381.ProofSupport.Fp2SourceLawful

set_option warningAsError true

/-! # Refinement of the decoded Fp2 square-root program -/

namespace Challenge.Bls12381.ProofSupport.Fp2

def SqrtCellRel (a : Fp.Limbs) (b : LawfulFp2.Base) : Prop :=
  Fp.Canonical a ∧ (Fp.value a : LawfulFp2.Base) = b

def SqrtPairRel (a : Repr) (b : LawfulFp2.Carrier) : Prop :=
  Canonical a ∧ toLawful a = b

/-- The concrete source `INV_TWO` limbs refine the purely algebraic inverse
of two used by the lawful square-root interpreter. -/
theorem invTwo_refines_lawful :
    (Fp.value invTwo : LawfulFp2.Base) = lawfulInvTwo := by
  rw [lawfulInvTwo_eq]
  apply eq_inv_of_mul_eq_one_left
  rw [value_invTwo, mul_comm]
  change ((2 : Nat) : LawfulFp2.Base) *
    (((EvmSemantics.Crypto.Bls12381.p + 1) / 2 : Nat) : LawfulFp2.Base) = 1
  rw [← Nat.cast_mul]
  rw [show 2 * ((EvmSemantics.Crypto.Bls12381.p + 1) / 2) =
      EvmSemantics.Crypto.Bls12381.p + 1 by
    norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU]]
  push_cast
  simp

/-- The concrete source exponentiation refines the lawful base-field square
root operation while preserving canonical limbs. -/
theorem sqrtCell_refines_lawful {a : Fp.Limbs} {b : LawfulFp2.Base}
    (h : SqrtCellRel a b) :
    SqrtCellRel (Fp.sqrtCanonical a) (lawfulSqrt b) := by
  rcases h with ⟨ha, hab⟩
  exact ⟨Fp.canonical_sqrtCanonical ha, by
    rw [Fp.sqrtCanonical_refines_lawful ha, hab]⟩

private theorem canonical_zero_repr : Canonical zero := by
  constructor <;> exact ⟨Fp.canonical_normalize 0⟩

theorem sqrtSourceOps_refines :
    SqrtProgram.Refines sqrtSourceOps lawfulSqrtOps SqrtCellRel SqrtPairRel := by
  constructor <;> dsimp only [sqrtSourceOps, lawfulSqrtOps]
  · rintro a b ⟨ha, hab⟩
    exact ⟨ha.c0.proof, by
      have hre := congrArg QuadraticAlgebra.re hab
      simpa [toLawful, LawfulFp2.ofWire, toField] using hre⟩
  · rintro a b ⟨ha, hab⟩
    exact ⟨ha.c1.proof, by
      have him := congrArg QuadraticAlgebra.im hab
      simpa [toLawful, LawfulFp2.ofWire, toField] using him⟩
  · exact ⟨canonical_zero_repr, toLawful_zero_repr⟩
  · rintro a₀ b₀ a₁ b₁ ⟨ha₀, hab₀⟩ ⟨ha₁, hab₁⟩
    refine ⟨canonical_mkRepr ⟨ha₀⟩ ⟨ha₁⟩, ?_⟩
    rw [toLawful_mkRepr]
    apply QuadraticAlgebra.ext <;> simp [hab₀, hab₁]
  · rintro a b ⟨ha, hab⟩
    apply Bool.eq_iff_iff.mpr
    simpa only [isZeroSource_iff ha, decide_eq_true_eq] using
      (show toLawful a = 0 ↔ b = 0 by rw [hab])
  · rintro a b ⟨ha, hab⟩
    apply Bool.eq_iff_iff.mpr
    rw [Fp.isZeroValue_eq_true, decide_eq_true_eq]
    constructor
    · intro hzero
      rw [← hab, hzero]
      norm_num
    · intro hzero
      apply Fp.value_eq_of_lawful_eq ha (Fp.canonical_normalize 0)
      rw [hab, hzero]
      norm_num
  · rintro a₀ b₀ a₁ b₁ ⟨ha₀, hab₀⟩ ⟨ha₁, hab₁⟩
    apply Bool.eq_iff_iff.mpr
    rw [Fp.eqCanonicalValue_eq_true]
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      rw [← hab₀, ← hab₁, h]
    · intro h
      exact Fp.value_eq_of_lawful_eq ha₀ ha₁ (hab₀.trans (h.trans hab₁.symm))
  · rintro a₀ b₀ a₁ b₁ ⟨ha₀, hab₀⟩ ⟨ha₁, hab₁⟩
    apply Bool.eq_iff_iff.mpr
    simpa only [eqSource_iff ha₀ ha₁, decide_eq_true_eq] using
      (show toLawful a₀ = toLawful a₁ ↔ b₀ = b₁ by rw [hab₀, hab₁])
  · rintro a₀ b₀ a₁ b₁ ⟨ha₀, hab₀⟩ ⟨ha₁, hab₁⟩
    exact ⟨Fp.canonical_addSource ha₀ ha₁, by
      change PrimeField.finEquiv (Fp.toField (Fp.addSource a₀ a₁)) = _
      rw [Fp.toLawful_addSource ha₀ ha₁,
        Fp.finEquiv_toField, Fp.finEquiv_toField, hab₀, hab₁]⟩
  · rintro a₀ b₀ a₁ b₁ ⟨ha₀, hab₀⟩ ⟨ha₁, hab₁⟩
    exact ⟨Fp.canonical_subSource ha₀ ha₁, by
      change PrimeField.finEquiv (Fp.toField (Fp.subSource a₀ a₁)) = _
      rw [Fp.toLawful_subSource ha₀ ha₁,
        Fp.finEquiv_toField, Fp.finEquiv_toField, hab₀, hab₁]⟩
  · rintro a b ⟨ha, hab⟩
    exact ⟨Fp.canonical_negSource ha, by
      change PrimeField.finEquiv (Fp.toField (Fp.negSource a)) = _
      rw [Fp.toLawful_negSource ha, Fp.finEquiv_toField, hab]⟩
  · rintro a₀ b₀ a₁ b₁ ⟨ha₀, hab₀⟩ ⟨ha₁, hab₁⟩
    exact ⟨Fp.canonical_mulCanonical ha₀ ha₁, by
      change PrimeField.finEquiv (Fp.toField (Fp.mulCanonical a₀ a₁)) = _
      rw [Fp.toField_mulCanonical ha₀ ha₁, map_mul,
        Fp.finEquiv_toField, Fp.finEquiv_toField, hab₀, hab₁]⟩
  · rintro a b ⟨ha, hab⟩
    exact ⟨Fp.canonical_squareCanonical ha, by
      rw [Fp.lawful_squareCanonical ha, hab]⟩
  · rintro a b ⟨ha, hab⟩
    exact sqrtCell_refines_lawful ⟨ha, hab⟩
  · rintro a b ⟨ha, hab⟩
    exact ⟨Fp.canonical_invCanonical ha, by
      change PrimeField.finEquiv (Fp.toField (Fp.invCanonical a)) = _
      rw [Fp.toLawful_invCanonical ha, Fp.finEquiv_toField, hab]⟩
  · rintro a b ⟨ha, hab⟩
    exact ⟨canonical_sqrSource ha, by
      rw [toLawful_sqrSource ha, hab]⟩
  · exact ⟨canonical_invTwo, invTwo_refines_lawful⟩

theorem sqrtSource_refines_lawful {a : Repr} (ha : Canonical a) :
    (sqrtSource a).exists_ =
        (SqrtProgram.run lawfulSqrtOps (toLawful a)).exists_ ∧
      SqrtPairRel (sqrtSource a).root
        (SqrtProgram.run lawfulSqrtOps (toLawful a)).root := by
  exact SqrtProgram.run_refines sqrtSourceOps_refines ⟨ha, rfl⟩

end Challenge.Bls12381.ProofSupport.Fp2
