import Challenge.Bls12381.ProofSupport.Fp2Source
import Challenge.Bls12381.ProofSupport.FpAddSubLawful
import Challenge.Bls12381.ProofSupport.FpInv

set_option warningAsError true

/-! # Lawful refinement of source-faithful BLS12-381 Fp2 arithmetic -/

namespace Challenge.Bls12381.ProofSupport.Fp2

theorem toField_addSource {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) :
    toField (addSource a b) = toField a + toField b := by
  change
    ({ c0 := Fp.toField (Fp.addSource a.c0 b.c0)
       c1 := Fp.toField (Fp.addSource a.c1 b.c1) } :
      EvmSemantics.Crypto.Bls12381.Fp2) =
    ({ c0 := Fp.toField a.c0 + Fp.toField b.c0
       c1 := Fp.toField a.c1 + Fp.toField b.c1 } :
      EvmSemantics.Crypto.Bls12381.Fp2)
  rw [Fp.toField_addSource ha.c0.proof hb.c0.proof,
    Fp.toField_addSource ha.c1.proof hb.c1.proof]

theorem toField_subSource {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) :
    toField (subSource a b) = toField a - toField b := by
  change
    ({ c0 := Fp.toField (Fp.subSource a.c0 b.c0)
       c1 := Fp.toField (Fp.subSource a.c1 b.c1) } :
      EvmSemantics.Crypto.Bls12381.Fp2) =
    ({ c0 := Fp.toField a.c0 - Fp.toField b.c0
       c1 := Fp.toField a.c1 - Fp.toField b.c1 } :
      EvmSemantics.Crypto.Bls12381.Fp2)
  rw [Fp.toField_subSource ha.c0.proof hb.c0.proof,
    Fp.toField_subSource ha.c1.proof hb.c1.proof]

theorem toField_negSource {a : Repr} (ha : Canonical a) :
    toField (negSource a) = -toField a := by
  change
    ({ c0 := Fp.toField (Fp.negSource a.c0)
       c1 := Fp.toField (Fp.negSource a.c1) } :
      EvmSemantics.Crypto.Bls12381.Fp2) =
    ({ c0 := -Fp.toField a.c0, c1 := -Fp.toField a.c1 } :
      EvmSemantics.Crypto.Bls12381.Fp2)
  rw [Fp.toField_negSource ha.c0.proof,
    Fp.toField_negSource ha.c1.proof]

theorem toField_mulFpSource {a : Repr} {s : Fp.Limbs}
    (ha : Canonical a) (hs : Fp.Canonical s) :
    toField (mulFpSource a s) =
      { c0 := Fp.toField a.c0 * Fp.toField s
        c1 := Fp.toField a.c1 * Fp.toField s } := by
  change
    ({ c0 := Fp.toField (Fp.mulCanonical a.c0 s)
       c1 := Fp.toField (Fp.mulCanonical a.c1 s) } :
      EvmSemantics.Crypto.Bls12381.Fp2) = _
  rw [Fp.toField_mulCanonical ha.c0.proof hs,
    Fp.toField_mulCanonical ha.c1.proof hs]

theorem toLawful_addSource {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) :
    toLawful (addSource a b) = toLawful a + toLawful b := by
  apply QuadraticAlgebra.ext <;>
    simp [toLawful, LawfulFp2.ofWire, toField, addSource, mkRepr,
      Fp.toLawful_addSource ha.c0.proof hb.c0.proof,
      Fp.toLawful_addSource ha.c1.proof hb.c1.proof]

theorem toLawful_subSource {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) :
    toLawful (subSource a b) = toLawful a - toLawful b := by
  apply QuadraticAlgebra.ext <;>
    simp [toLawful, LawfulFp2.ofWire, toField, subSource, mkRepr,
      Fp.toLawful_subSource ha.c0.proof hb.c0.proof,
      Fp.toLawful_subSource ha.c1.proof hb.c1.proof]

theorem toLawful_negSource {a : Repr} (ha : Canonical a) :
    toLawful (negSource a) = -toLawful a := by
  apply QuadraticAlgebra.ext <;>
    simp [toLawful, LawfulFp2.ofWire, toField, negSource, mkRepr,
      Fp.toLawful_negSource ha.c0.proof,
      Fp.toLawful_negSource ha.c1.proof]

theorem toLawful_mulFpSource {a : Repr} {s : Fp.Limbs}
    (ha : Canonical a) (hs : Fp.Canonical s) :
    toLawful (mulFpSource a s) =
      algebraMap LawfulFp2.Base LawfulFp2.Carrier
        (PrimeField.finEquiv (Fp.toField s)) * toLawful a := by
  apply QuadraticAlgebra.ext <;>
    simp [toLawful, LawfulFp2.ofWire, toField, mulFpSource, mkRepr,
      Fp.toField_mulCanonical ha.c0.proof hs,
      Fp.toField_mulCanonical ha.c1.proof hs, map_mul, mul_comm]

def evalLawful (a : Fp.Limbs) : LawfulFp2.Base :=
  PrimeField.finEquiv (Fp.toField a)

def evalField (a : Fp.Limbs) : Fin EvmSemantics.Crypto.Bls12381.p := Fp.toField a

def fieldSourceSemantics : SourceProgram.Semantics
    (Fin EvmSemantics.Crypto.Bls12381.p) where
  add := fun a b => a + b
  sub := fun a b => a - b
  mul := fun a b => a * b
  square := fun a => a ^ 2
  inv := Inv.inv
  neg := Neg.neg

def lawfulSourceSemantics : SourceProgram.Semantics LawfulFp2.Base where
  add := fun a b => a + b
  sub := fun a b => a - b
  mul := fun a b => a * b
  square := fun a => a ^ 2
  inv := Inv.inv
  neg := Neg.neg

theorem lawful_directSourceOps_add (output : SourceRef) {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.Canonical (Id.run (directSourceOps.add output a b)) ∧
      evalLawful (Id.run (directSourceOps.add output a b)) =
        evalLawful a + evalLawful b := by
  constructor
  · exact canonical_directSourceOps_add output ha hb
  · rw [directSourceOps_add, sourceAdd_eq]
    exact Fp.toLawful_addSource ha hb

theorem lawful_directSourceOps_sub (output : SourceRef) {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.Canonical (Id.run (directSourceOps.sub output a b)) ∧
      evalLawful (Id.run (directSourceOps.sub output a b)) =
        evalLawful a - evalLawful b := by
  constructor
  · exact canonical_directSourceOps_sub output ha hb
  · rw [directSourceOps_sub, sourceSub_eq]
    exact Fp.toLawful_subSource ha hb

theorem lawful_directSourceOps_mul (output : SourceRef) {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.Canonical (Id.run (directSourceOps.mul output a b)) ∧
      evalLawful (Id.run (directSourceOps.mul output a b)) =
        evalLawful a * evalLawful b := by
  constructor
  · exact canonical_directSourceOps_mul output ha hb
  · unfold evalLawful
    rw [directSourceOps_mul, sourceMul_eq,
      Fp.toField_mulCanonical ha hb, map_mul]

theorem lawful_directSourceOps_square (output : SourceRef) {a : Fp.Limbs}
    (ha : Fp.Canonical a) :
    Fp.Canonical (Id.run (directSourceOps.square output a)) ∧
      evalLawful (Id.run (directSourceOps.square output a)) =
        (evalLawful a) ^ 2 := by
  constructor
  · exact canonical_directSourceOps_square output ha
  · unfold evalLawful
    rw [directSourceOps_square, sourceSquare_eq,
      Fp.toField_squareCanonical ha, map_pow]

theorem lawful_directSourceOps_inv (output : SourceRef) {a : Fp.Limbs}
    (ha : Fp.Canonical a) :
    Fp.Canonical (Id.run (directSourceOps.inv output a)) ∧
      evalLawful (Id.run (directSourceOps.inv output a)) =
        (evalLawful a)⁻¹ := by
  constructor
  · exact canonical_directSourceOps_inv output ha
  · rw [directSourceOps_inv, sourceInv_eq]
    exact Fp.toLawful_invCanonical ha

theorem lawful_directSourceOps_neg (output : SourceRef) {a : Fp.Limbs}
    (ha : Fp.Canonical a) :
    Fp.Canonical (Id.run (directSourceOps.neg output a)) ∧
      evalLawful (Id.run (directSourceOps.neg output a)) =
        -(evalLawful a) := by
  constructor
  · exact canonical_directSourceOps_neg output ha
  · rw [directSourceOps_neg, sourceNeg_eq]
    exact Fp.toLawful_negSource ha

theorem field_directSourceOps_add (output : SourceRef) {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.Canonical (Id.run (directSourceOps.add output a b)) ∧
      evalField (Id.run (directSourceOps.add output a b)) =
        evalField a + evalField b := by
  constructor
  · exact canonical_directSourceOps_add output ha hb
  · rw [directSourceOps_add, sourceAdd_eq]
    exact Fp.toField_addSource ha hb

theorem field_directSourceOps_sub (output : SourceRef) {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.Canonical (Id.run (directSourceOps.sub output a b)) ∧
      evalField (Id.run (directSourceOps.sub output a b)) =
        evalField a - evalField b := by
  constructor
  · exact canonical_directSourceOps_sub output ha hb
  · rw [directSourceOps_sub, sourceSub_eq]
    exact Fp.toField_subSource ha hb

theorem field_directSourceOps_mul (output : SourceRef) {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.Canonical (Id.run (directSourceOps.mul output a b)) ∧
      evalField (Id.run (directSourceOps.mul output a b)) =
        evalField a * evalField b := by
  constructor
  · exact canonical_directSourceOps_mul output ha hb
  · unfold evalField
    rw [directSourceOps_mul, sourceMul_eq]
    exact Fp.toField_mulCanonical ha hb

theorem toField_mulC0Source {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) :
    Fp.toField (mulRealSource (mulV0Source a b) (mulV1Source a b)) =
      Fp.toField a.c0 * Fp.toField b.c0 -
        Fp.toField a.c1 * Fp.toField b.c1 := by
  have hv0 := (canonical_mulV0Source ha hb).proof
  have hv1 := (canonical_mulV1Source ha hb).proof
  rw [show mulRealSource (mulV0Source a b) (mulV1Source a b) =
      Fp.subSource (mulV0Source a b) (mulV1Source a b) by rfl]
  rw [Fp.toField_subSource hv0 hv1]
  rw [show Fp.toField (mulV0Source a b) =
      Fp.toField a.c0 * Fp.toField b.c0 by
        exact Fp.toField_mulCanonical ha.c0.proof hb.c0.proof,
    show Fp.toField (mulV1Source a b) =
      Fp.toField a.c1 * Fp.toField b.c1 by
        exact Fp.toField_mulCanonical ha.c1.proof hb.c1.proof]

theorem toField_mulC1Source {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) :
    Fp.toField
      (mulImaginarySource a b (mulV0Source a b) (mulV1Source a b)) =
      (Fp.toField a.c0 + Fp.toField a.c1) *
          (Fp.toField b.c0 + Fp.toField b.c1) -
        Fp.toField a.c0 * Fp.toField b.c0 -
        Fp.toField a.c1 * Fp.toField b.c1 := by
  have haSum := Fp.canonical_addSource ha.c0.proof ha.c1.proof
  have hbSum := Fp.canonical_addSource hb.c0.proof hb.c1.proof
  have hv0 := (canonical_mulV0Source ha hb).proof
  have hv1 := (canonical_mulV1Source ha hb).proof
  have hcross := Fp.canonical_mulCanonical haSum hbSum
  have hvSum := Fp.canonical_addSource hv0 hv1
  rw [show mulImaginarySource a b (mulV0Source a b) (mulV1Source a b) =
      Fp.subSource
        (Fp.mulCanonical (Fp.addSource a.c0 a.c1)
          (Fp.addSource b.c0 b.c1))
        (Fp.addSource (mulV0Source a b) (mulV1Source a b)) by rfl]
  rw [Fp.toField_subSource hcross hvSum,
    Fp.toField_mulCanonical haSum hbSum,
    Fp.toField_addSource ha.c0.proof ha.c1.proof,
    Fp.toField_addSource hb.c0.proof hb.c1.proof,
    Fp.toField_addSource hv0 hv1,
    show Fp.toField (mulV0Source a b) =
      Fp.toField a.c0 * Fp.toField b.c0 by
        exact Fp.toField_mulCanonical ha.c0.proof hb.c0.proof,
    show Fp.toField (mulV1Source a b) =
      Fp.toField a.c1 * Fp.toField b.c1 by
        exact Fp.toField_mulCanonical ha.c1.proof hb.c1.proof]
  simp only [sub_eq_add_neg, neg_add_rev, add_assoc]
  ac_rfl

theorem toField_mulSource {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) :
    toField (mulSource a b) = toField a * toField b := by
  have hresult := SourceProgram.runMulWith_refines directSourceOps
    Fp.Canonical evalField fieldSourceSemantics
    field_directSourceOps_add field_directSourceOps_sub
    field_directSourceOps_mul a.c0 a.c1 b.c0 b.c1
    (by simpa only [directSourceOps_input] using ha.c0.proof)
    (by simpa only [directSourceOps_input] using ha.c1.proof)
    (by simpa only [directSourceOps_input] using hb.c0.proof)
    (by simpa only [directSourceOps_input] using hb.c1.proof)
  have hc0 := hresult.2.2.1
  have hc1 := hresult.2.2.2
  simp only [fieldSourceSemantics, directSourceOps_input] at hc0 hc1
  change evalField (Id.run (runMulSourceWith directSourceOps a b)).1 = _ at hc0
  change evalField (Id.run (runMulSourceWith directSourceOps a b)).2 = _ at hc1
  unfold mulSource
  rw [toField_mkRepr]
  change _ = _root_.Fp2.mul (toField a) (toField b)
  unfold _root_.Fp2.mul
  rw [_root_.Fp2.mk.injEq]
  constructor
  · rw [directSourceOps_value]
    change evalField (Id.run (runMulSourceWith directSourceOps a b)).1 = _
    rw [hc0]
    rfl
  · rw [directSourceOps_value]
    change evalField (Id.run (runMulSourceWith directSourceOps a b)).2 = _
    rw [show (toField a).c0 = evalField a.c0 by rfl,
      show (toField a).c1 = evalField a.c1 by rfl,
      show (toField b).c0 = evalField b.c0 by rfl,
      show (toField b).c1 = evalField b.c1 by rfl]
    rw [hc1]
    simp only [sub_eq_add_neg, neg_add_rev, add_assoc]
    ac_rfl

/-- Consumer contract for the authoritative source multiplication program.
Callers receive the representation invariant and mathematical field meaning
together without reopening the Karatsuba schedule or its interpreter. -/
theorem mulSource_spec {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) :
    Canonical (mulSource a b) ∧
      toField (mulSource a b) = toField a * toField b :=
  ⟨canonical_mulSource ha hb, toField_mulSource ha hb⟩

theorem toField_sqrRealSource {a : Repr} (ha : Canonical a) :
    Fp.toField (sqrRealSource a) =
      (Fp.toField a.c0 + Fp.toField a.c1) *
        (Fp.toField a.c0 - Fp.toField a.c1) := by
  rw [show sqrRealSource a = Fp.mulCanonical
      (Fp.addSource a.c0 a.c1) (Fp.subSource a.c0 a.c1) by rfl]
  rw [Fp.toField_mulCanonical
      (Fp.canonical_addSource ha.c0.proof ha.c1.proof)
      (Fp.canonical_subSource ha.c0.proof ha.c1.proof),
    Fp.toField_addSource ha.c0.proof ha.c1.proof,
    Fp.toField_subSource ha.c0.proof ha.c1.proof]

theorem toField_sqrC1Source {a : Repr} (ha : Canonical a) :
    Fp.toField (sqrC1Source a) =
      Fp.toField a.c0 * Fp.toField a.c1 +
        Fp.toField a.c0 * Fp.toField a.c1 := by
  have hproduct := (canonical_sqrProductSource ha).proof
  rw [show sqrC1Source a = Fp.addSource
      (sqrProductSource a) (sqrProductSource a) by rfl]
  rw [Fp.toField_addSource hproduct hproduct,
    show Fp.toField (sqrProductSource a) =
      Fp.toField a.c0 * Fp.toField a.c1 by
        exact Fp.toField_mulCanonical ha.c0.proof ha.c1.proof]

theorem toField_sqrSource {a : Repr} (ha : Canonical a) :
    toField (sqrSource a) = _root_.Fp2.square (toField a) := by
  rw [sqrSource_eq, toField_mkRepr,
    toField_sqrRealSource ha, toField_sqrC1Source ha]
  change _ = _root_.Fp2.square (toField a)
  simp only [toField, _root_.Fp2.square]
  congr 1
  exact (add_mul _ _ _).symm

theorem toLawful_mulSource {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) :
    toLawful (mulSource a b) = toLawful a * toLawful b := by
  have hresult := SourceProgram.runMulWith_refines directSourceOps
    Fp.Canonical evalLawful lawfulSourceSemantics
    lawful_directSourceOps_add lawful_directSourceOps_sub
    lawful_directSourceOps_mul a.c0 a.c1 b.c0 b.c1
    (by simpa only [directSourceOps_input] using ha.c0.proof)
    (by simpa only [directSourceOps_input] using ha.c1.proof)
    (by simpa only [directSourceOps_input] using hb.c0.proof)
    (by simpa only [directSourceOps_input] using hb.c1.proof)
  have hc0 := hresult.2.2.1
  have hc1 := hresult.2.2.2
  simp only [lawfulSourceSemantics, directSourceOps_input] at hc0 hc1
  change evalLawful (Id.run (runMulSourceWith directSourceOps a b)).1 = _ at hc0
  change evalLawful (Id.run (runMulSourceWith directSourceOps a b)).2 = _ at hc1
  unfold mulSource
  rw [toLawful_mkRepr]
  apply QuadraticAlgebra.ext
  · rw [directSourceOps_value]
    simp only [QuadraticAlgebra.re_mul, neg_mul, one_mul]
    rw [show (toLawful a).re = evalLawful a.c0 by rfl,
      show (toLawful b).re = evalLawful b.c0 by rfl,
      show (toLawful a).im = evalLawful a.c1 by rfl,
      show (toLawful b).im = evalLawful b.c1 by rfl]
    rw [show PrimeField.finEquiv
        (Fp.toField (Id.run (runMulSourceWith directSourceOps a b)).1) =
      evalLawful (Id.run (runMulSourceWith directSourceOps a b)).1 by rfl]
    simpa only [sub_eq_add_neg] using hc0
  · rw [directSourceOps_value]
    simp only [QuadraticAlgebra.im_mul, zero_mul, add_zero]
    rw [show (toLawful a).re = evalLawful a.c0 by rfl,
      show (toLawful b).re = evalLawful b.c0 by rfl,
      show (toLawful a).im = evalLawful a.c1 by rfl,
      show (toLawful b).im = evalLawful b.c1 by rfl]
    rw [directSourceOps_value]
    rw [show PrimeField.finEquiv
        (Fp.toField (Id.run (runMulSourceWith directSourceOps a b)).2) =
      evalLawful (Id.run (runMulSourceWith directSourceOps a b)).2 by rfl]
    rw [hc1]
    ring

theorem toLawful_sqrSource {a : Repr} (ha : Canonical a) :
    toLawful (sqrSource a) = toLawful a * toLawful a := by
  rw [sqrSource_eq, toLawful_mkRepr]
  apply QuadraticAlgebra.ext
  · simp [toLawful, LawfulFp2.ofWire, toField,
      toField_sqrRealSource ha,
      map_add, map_sub, map_mul]
    ring
  · simp [toLawful, LawfulFp2.ofWire, toField,
      toField_sqrC1Source ha, map_add, map_mul]
    ring

theorem toLawful_invNormSource {a : Repr} (ha : Canonical a) :
    PrimeField.finEquiv (Fp.toField (invNormSource a)) =
      QuadraticAlgebra.norm (toLawful a) := by
  have hs0 := Fp.canonical_squareCanonical ha.c0.proof
  have hs1 := Fp.canonical_squareCanonical ha.c1.proof
  rw [show invNormSource a = Fp.addSource
      (Fp.squareCanonical a.c0) (Fp.squareCanonical a.c1) by rfl]
  rw [Fp.toLawful_addSource hs0 hs1,
    Fp.toField_squareCanonical ha.c0.proof,
    Fp.toField_squareCanonical ha.c1.proof,
    map_pow, map_pow]
  simp [toLawful, LawfulFp2.ofWire, toField,
    QuadraticAlgebra.norm_def, pow_two]

theorem toLawful_invNormInvSource {a : Repr} (ha : Canonical a) :
    PrimeField.finEquiv
        (Fp.toField (Fp.invCanonical (invNormSource a))) =
      (QuadraticAlgebra.norm (toLawful a))⁻¹ := by
  rw [Fp.toLawful_invCanonical (canonical_invNormSource ha).proof,
    toLawful_invNormSource ha]

theorem toLawful_invC0Source {a : Repr} (ha : Canonical a) :
    PrimeField.finEquiv (Fp.toField
      (invRealSource a.c0 (Fp.invCanonical (invNormSource a)))) =
      (toLawful a).re * (QuadraticAlgebra.norm (toLawful a))⁻¹ := by
  rw [show invRealSource a.c0 (Fp.invCanonical (invNormSource a)) =
      Fp.mulCanonical a.c0 (Fp.invCanonical (invNormSource a)) by rfl]
  rw [Fp.toField_mulCanonical ha.c0.proof
      (Fp.canonical_invCanonical (canonical_invNormSource ha).proof),
    map_mul, toLawful_invNormInvSource ha]
  rfl

theorem toLawful_invC1Source {a : Repr} (ha : Canonical a) :
    PrimeField.finEquiv (Fp.toField
      (invImaginarySource a.c1 (Fp.invCanonical (invNormSource a)))) =
      -(toLawful a).im * (QuadraticAlgebra.norm (toLawful a))⁻¹ := by
  rw [show invImaginarySource a.c1 (Fp.invCanonical (invNormSource a)) =
      Fp.mulCanonical (Fp.negSource a.c1)
        (Fp.invCanonical (invNormSource a)) by rfl]
  rw [Fp.toField_mulCanonical (Fp.canonical_negSource ha.c1.proof)
      (Fp.canonical_invCanonical (canonical_invNormSource ha).proof),
    map_mul, Fp.toField_negSource ha.c1.proof, map_neg,
    toLawful_invNormInvSource ha]
  rfl

/-- The source inversion schedule refines the lawful quadratic-field inverse.
No equality to the pinned opaque `FF.modInv` is assumed or required. -/
theorem toLawful_invSource {a : Repr} (ha : Canonical a) :
    toLawful (invSource a) = (toLawful a)⁻¹ := by
  have hresult := SourceProgram.runInvWith_refines directSourceOps
    Fp.Canonical evalLawful lawfulSourceSemantics
    lawful_directSourceOps_add lawful_directSourceOps_mul
    lawful_directSourceOps_square lawful_directSourceOps_inv
    lawful_directSourceOps_neg a.c0 a.c1
    (by simpa only [directSourceOps_input] using ha.c0.proof)
    (by simpa only [directSourceOps_input] using ha.c1.proof)
  have hc0 := hresult.2.2.1
  have hc1 := hresult.2.2.2
  simp only [lawfulSourceSemantics, directSourceOps_input] at hc0 hc1
  change evalLawful (Id.run (runInvSourceWith directSourceOps a)).1 = _ at hc0
  change evalLawful (Id.run (runInvSourceWith directSourceOps a)).2 = _ at hc1
  unfold invSource
  rw [toLawful_mkRepr]
  apply QuadraticAlgebra.ext
  · rw [directSourceOps_value]
    rw [QuadraticAlgebra.re_inv, QuadraticAlgebra.norm_def]
    simp only [zero_mul, add_zero, neg_mul, one_mul, sub_neg_eq_add]
    rw [show (toLawful a).re = evalLawful a.c0 by rfl,
      show (toLawful a).im = evalLawful a.c1 by rfl]
    rw [show PrimeField.finEquiv
        (Fp.toField (Id.run (runInvSourceWith directSourceOps a)).1) =
      evalLawful (Id.run (runInvSourceWith directSourceOps a)).1 by rfl]
    rw [hc0]
    simp only [pow_two]
    rw [add_comm (evalLawful a.c0 * evalLawful a.c0)
      (evalLawful a.c1 * evalLawful a.c1)]
    rw [mul_comm]
  · rw [directSourceOps_value]
    rw [QuadraticAlgebra.im_inv, QuadraticAlgebra.norm_def]
    simp only [zero_mul, add_zero, neg_mul, one_mul, sub_neg_eq_add]
    rw [show (toLawful a).re = evalLawful a.c0 by rfl,
      show (toLawful a).im = evalLawful a.c1 by rfl]
    rw [directSourceOps_value]
    rw [show PrimeField.finEquiv
        (Fp.toField (Id.run (runInvSourceWith directSourceOps a)).2) =
      evalLawful (Id.run (runInvSourceWith directSourceOps a)).2 by rfl]
    rw [hc1]
    simp only [pow_two]
    ring

theorem toLawful_invSource_zero {a : Repr} (ha : Canonical a)
    (hzero : toLawful a = 0) : toLawful (invSource a) = 0 := by
  rw [toLawful_invSource ha, hzero, inv_zero]

theorem toLawful_mul_invSource {a : Repr} (ha : Canonical a)
    (hne : toLawful a ≠ 0) :
    toLawful a * toLawful (invSource a) = 1 := by
  rw [toLawful_invSource ha]
  exact LawfulFp2.mul_inv_cancel (toLawful a) hne

end Challenge.Bls12381.ProofSupport.Fp2
