import Challenge.Bls12381.ProofSupport.Fp2SourceSchedule

set_option warningAsError true

/-! # Correctness of source-faithful BLS12-381 Fp2 arithmetic -/

namespace Challenge.Bls12381.ProofSupport.Fp2

theorem canonical_addSource {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) : Canonical (addSource a b) :=
  canonical_mkRepr
    ⟨Fp.canonical_addSource ha.c0.proof hb.c0.proof⟩
    ⟨Fp.canonical_addSource ha.c1.proof hb.c1.proof⟩

theorem canonical_subSource {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) : Canonical (subSource a b) :=
  canonical_mkRepr
    ⟨Fp.canonical_subSource ha.c0.proof hb.c0.proof⟩
    ⟨Fp.canonical_subSource ha.c1.proof hb.c1.proof⟩

theorem canonical_negSource {a : Repr} (ha : Canonical a) :
    Canonical (negSource a) :=
  canonical_mkRepr
    ⟨Fp.canonical_negSource ha.c0.proof⟩
    ⟨Fp.canonical_negSource ha.c1.proof⟩

theorem canonical_mulV0Source {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) : ComponentCanonical (mulV0Source a b) :=
  ⟨Fp.canonical_mulCanonical ha.c0.proof hb.c0.proof⟩

theorem canonical_mulV1Source {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) : ComponentCanonical (mulV1Source a b) :=
  ⟨Fp.canonical_mulCanonical ha.c1.proof hb.c1.proof⟩

theorem canonical_mulRealSource {v0 v1 : Fp.Limbs}
    (hv0 : ComponentCanonical v0) (hv1 : ComponentCanonical v1) :
    ComponentCanonical (mulRealSource v0 v1) :=
  ⟨Fp.canonical_subSource hv0.proof hv1.proof⟩

theorem canonical_mulImaginarySource {a b : Repr} {v0 v1 : Fp.Limbs}
    (ha : Canonical a) (hb : Canonical b)
    (hv0 : ComponentCanonical v0) (hv1 : ComponentCanonical v1) :
    ComponentCanonical (mulImaginarySource a b v0 v1) := by
  have haSum := Fp.canonical_addSource ha.c0.proof ha.c1.proof
  have hbSum := Fp.canonical_addSource hb.c0.proof hb.c1.proof
  have hcross := Fp.canonical_mulCanonical haSum hbSum
  have hvSum := Fp.canonical_addSource hv0.proof hv1.proof
  exact ⟨Fp.canonical_subSource hcross hvSum⟩

theorem canonical_mulC0Source {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) :
    ComponentCanonical
      (mulRealSource (mulV0Source a b) (mulV1Source a b)) :=
  canonical_mulRealSource (canonical_mulV0Source ha hb)
    (canonical_mulV1Source ha hb)

theorem canonical_mulC1Source {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) :
    ComponentCanonical
      (mulImaginarySource a b (mulV0Source a b) (mulV1Source a b)) :=
  canonical_mulImaginarySource ha hb (canonical_mulV0Source ha hb)
    (canonical_mulV1Source ha hb)

theorem canonical_mulSource {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) : Canonical (mulSource a b) := by
  have hresult := SourceProgram.runMulWith_good directSourceOps Fp.Canonical
    canonical_directSourceOps_add canonical_directSourceOps_sub
    canonical_directSourceOps_mul a.c0 a.c1 b.c0 b.c1
    (by simpa only [directSourceOps_input] using ha.c0.proof)
    (by simpa only [directSourceOps_input] using ha.c1.proof)
    (by simpa only [directSourceOps_input] using hb.c0.proof)
    (by simpa only [directSourceOps_input] using hb.c1.proof)
  unfold mulSource
  apply canonical_mkRepr
  · exact ⟨by
      rw [directSourceOps_value]
      exact hresult.1⟩
  · exact ⟨by
      rw [directSourceOps_value]
      exact hresult.2⟩

theorem canonical_sqrRealSource {a : Repr} (ha : Canonical a) :
    ComponentCanonical (sqrRealSource a) :=
  ⟨Fp.canonical_mulCanonical
    (Fp.canonical_addSource ha.c0.proof ha.c1.proof)
    (Fp.canonical_subSource ha.c0.proof ha.c1.proof)⟩

theorem canonical_sqrImaginarySource {product : Fp.Limbs}
    (hproduct : ComponentCanonical product) :
    ComponentCanonical (sqrImaginarySource product) :=
  ⟨Fp.canonical_addSource hproduct.proof hproduct.proof⟩

theorem canonical_sqrProductSource {a : Repr} (ha : Canonical a) :
    ComponentCanonical (sqrProductSource a) :=
  ⟨Fp.canonical_mulCanonical ha.c0.proof ha.c1.proof⟩

theorem canonical_sqrC1Source {a : Repr} (ha : Canonical a) :
    ComponentCanonical (sqrC1Source a) := by
  exact canonical_sqrImaginarySource
    ⟨Fp.canonical_mulCanonical ha.c0.proof ha.c1.proof⟩

theorem canonical_sqrSource {a : Repr} (ha : Canonical a) :
    Canonical (sqrSource a) :=
  canonical_mkRepr (canonical_sqrRealSource ha) (canonical_sqrC1Source ha)

theorem canonical_invNormSource {a : Repr} (ha : Canonical a) :
    ComponentCanonical (invNormSource a) :=
  ⟨Fp.canonical_addSource
    (Fp.canonical_squareCanonical ha.c0.proof)
    (Fp.canonical_squareCanonical ha.c1.proof)⟩

theorem canonical_invRealSource {a0 normInv : Fp.Limbs}
    (ha0 : ComponentCanonical a0)
    (hnormInv : ComponentCanonical normInv) :
    ComponentCanonical (invRealSource a0 normInv) :=
  ⟨Fp.canonical_mulCanonical ha0.proof hnormInv.proof⟩

theorem canonical_invImaginarySource {a1 normInv : Fp.Limbs}
    (ha1 : ComponentCanonical a1)
    (hnormInv : ComponentCanonical normInv) :
    ComponentCanonical (invImaginarySource a1 normInv) :=
  ⟨Fp.canonical_mulCanonical (Fp.canonical_negSource ha1.proof)
    hnormInv.proof⟩

theorem canonical_invC0Source {a : Repr} (ha : Canonical a) :
    ComponentCanonical
      (invRealSource a.c0 (Fp.invCanonical (invNormSource a))) := by
  have hnorm := canonical_invNormSource ha
  exact canonical_invRealSource ha.c0
    ⟨Fp.canonical_invCanonical hnorm.proof⟩

theorem canonical_invC1Source {a : Repr} (ha : Canonical a) :
    ComponentCanonical
      (invImaginarySource a.c1 (Fp.invCanonical (invNormSource a))) := by
  have hnorm := canonical_invNormSource ha
  exact canonical_invImaginarySource ha.c1
    ⟨Fp.canonical_invCanonical hnorm.proof⟩

theorem canonical_invSource {a : Repr} (ha : Canonical a) :
    Canonical (invSource a) := by
  have hresult := SourceProgram.runInvWith_good directSourceOps Fp.Canonical
    canonical_directSourceOps_add canonical_directSourceOps_mul
    canonical_directSourceOps_square canonical_directSourceOps_inv
    canonical_directSourceOps_neg a.c0 a.c1
    (by simpa only [directSourceOps_input] using ha.c0.proof)
    (by simpa only [directSourceOps_input] using ha.c1.proof)
  unfold invSource
  apply canonical_mkRepr
  · exact ⟨by
      rw [directSourceOps_value]
      exact hresult.1⟩
  · exact ⟨by
      rw [directSourceOps_value]
      exact hresult.2⟩

theorem canonical_mulFpSource {a : Repr} {s : Fp.Limbs}
    (ha : Canonical a) (hs : Fp.Canonical s) :
    Canonical (mulFpSource a s) :=
  canonical_mkRepr
    ⟨Fp.canonical_mulCanonical ha.c0.proof hs⟩
    ⟨Fp.canonical_mulCanonical ha.c1.proof hs⟩

end Challenge.Bls12381.ProofSupport.Fp2
