import Challenge.Bls12381.ProofSupport.MsmSemantics
import Challenge.Bls12381.ProofSupport.SubgroupSemantics
import Challenge.Bls12381.ProofSupport.CodecSubgroup

set_option warningAsError true

/-!
# Prime-subgroup closure of naive MSM

This proof-only module combines the independent group-sum semantics with the
proof-visible subgroup characterization.  It proves that the naive fold stays
in the prime subgroup whenever every input point is accepted.
-/

namespace Challenge.Bls12381.ProofSupport.MsmSubgroup

open EvmSemantics.Crypto.Bls12381

private def g1ValidTermsOfWire (terms : List Msm.G1WireTerm)
    (hvalid : ∀ term ∈ terms, Codec.ValidG1 term.1) :
    List MsmSemantics.G1ValidTerm :=
  match terms with
  | [] => []
  | term :: rest =>
      (SubgroupSemantics.g1PointOfWire term.1
          (hvalid term (by simp)), term.2) ::
        g1ValidTermsOfWire rest fun item hitem =>
          hvalid item (by simp [hitem])

private def g2ValidTermsOfWire (terms : List Msm.G2WireTerm)
    (hvalid : ∀ term ∈ terms, Codec.ValidG2 term.1) :
    List MsmSemantics.G2ValidTerm :=
  match terms with
  | [] => []
  | term :: rest =>
      (SubgroupSemantics.g2PointOfWire term.1
          (hvalid term (by simp)), term.2) ::
        g2ValidTermsOfWire rest fun item hitem =>
          hvalid item (by simp [hitem])

private theorem g1Value_validTermsOfWire (terms : List Msm.G1WireTerm)
    (hvalid : ∀ term ∈ terms, Codec.ValidG1 term.1) :
    G1Affine.toWire
        (MsmSemantics.g1Value (g1ValidTermsOfWire terms hvalid)) =
      Msm.g1Wire terms := by
  congr 1
  change Msm.g1
      ((g1ValidTermsOfWire terms hvalid).map MsmSemantics.forgetG1Term) =
    Msm.g1 (terms.map Msm.g1TermOfWire)
  congr 1
  induction terms with
  | nil => rfl
  | cons term rest ih =>
      simp only [g1ValidTermsOfWire, List.map_cons]
      congr 1
      exact ih (fun item hitem => hvalid item (by simp [hitem]))

private theorem g2Value_validTermsOfWire (terms : List Msm.G2WireTerm)
    (hvalid : ∀ term ∈ terms, Codec.ValidG2 term.1) :
    G2Affine.toWire
        (MsmSemantics.g2Value (g2ValidTermsOfWire terms hvalid)) =
      Msm.g2Wire terms := by
  congr 1
  change Msm.g2
      ((g2ValidTermsOfWire terms hvalid).map MsmSemantics.forgetG2Term) =
    Msm.g2 (terms.map Msm.g2TermOfWire)
  congr 1
  induction terms with
  | nil => rfl
  | cons term rest ih =>
      simp only [g2ValidTermsOfWire, List.map_cons]
      congr 1
      exact ih (fun item hitem => hvalid item (by simp [hitem]))

private theorem g1ValidTermsOfWire_accepted (terms : List Msm.G1WireTerm)
    (hvalid : ∀ term ∈ terms, Codec.ValidG1 term.1)
    (hsubgroup : ∀ term ∈ terms, Subgroup.g1 term.1 = true) :
    ∀ term ∈ g1ValidTermsOfWire terms hvalid,
      Subgroup.g1Affine term.1.1 = true := by
  induction terms with
  | nil => simp [g1ValidTermsOfWire]
  | cons wireTerm rest ih =>
      intro term hterm
      simp only [g1ValidTermsOfWire, List.mem_cons] at hterm
      rcases hterm with rfl | hrest
      · simpa [Subgroup.g1, SubgroupSemantics.g1PointOfWire] using
          hsubgroup wireTerm (by simp)
      · exact ih
          (fun item hitem => hvalid item (by simp [hitem]))
          (fun item hitem => hsubgroup item (by simp [hitem])) term hrest

private theorem g2ValidTermsOfWire_accepted (terms : List Msm.G2WireTerm)
    (hvalid : ∀ term ∈ terms, Codec.ValidG2 term.1)
    (hsubgroup : ∀ term ∈ terms, Subgroup.g2 term.1 = true) :
    ∀ term ∈ g2ValidTermsOfWire terms hvalid,
      Subgroup.g2Affine term.1.1 = true := by
  induction terms with
  | nil => simp [g2ValidTermsOfWire]
  | cons wireTerm rest ih =>
      intro term hterm
      simp only [g2ValidTermsOfWire, List.mem_cons] at hterm
      rcases hterm with rfl | hrest
      · simpa [Subgroup.g2, SubgroupSemantics.g2PointOfWire] using
          hsubgroup wireTerm (by simp)
      · exact ih
          (fun item hitem => hvalid item (by simp [hitem]))
          (fun item hitem => hsubgroup item (by simp [hitem])) term hrest

theorem g1MathSum_nsmul_zero (terms : List MsmSemantics.G1ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g1Affine term.1.1 = true) :
    N • MsmSemantics.g1MathSum terms = 0 := by
  induction terms with
  | nil => simp [MsmSemantics.g1MathSum]
  | cons term rest ih =>
      rcases term with ⟨point, scalar⟩
      have hpoint : N • AffineGroup.toMathlib G1Affine.curve point = 0 :=
        (SubgroupSemantics.g1Affine_eq_true_iff_nsmul_zero point).1
          (hterms (point, scalar) (by simp))
      have hscaled : N •
          (scalar.val • AffineGroup.toMathlib G1Affine.curve point) = 0 := by
        rw [smul_smul, Nat.mul_comm, ← smul_smul, hpoint, smul_zero]
      have hrest : N • MsmSemantics.g1MathSum rest = 0 := by
        apply ih
        intro term hterm
        exact hterms term (by simp [hterm])
      calc
        N • MsmSemantics.g1MathSum ((point, scalar) :: rest) =
            N • (scalar.val • AffineGroup.toMathlib G1Affine.curve point) +
              N • MsmSemantics.g1MathSum rest := by
                simp [MsmSemantics.g1MathSum, nsmul_add]
        _ = 0 := by rw [hscaled, hrest, add_zero]

theorem g2MathSum_nsmul_zero (terms : List MsmSemantics.G2ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g2Affine term.1.1 = true) :
    N • MsmSemantics.g2MathSum terms = 0 := by
  induction terms with
  | nil => simp [MsmSemantics.g2MathSum]
  | cons term rest ih =>
      rcases term with ⟨point, scalar⟩
      have hpoint : N • AffineGroup.toMathlib G2Affine.curve point = 0 :=
        (SubgroupSemantics.g2Affine_eq_true_iff_nsmul_zero point).1
          (hterms (point, scalar) (by simp))
      have hscaled : N •
          (scalar.val • AffineGroup.toMathlib G2Affine.curve point) = 0 := by
        rw [smul_smul, Nat.mul_comm, ← smul_smul, hpoint, smul_zero]
      have hrest : N • MsmSemantics.g2MathSum rest = 0 := by
        apply ih
        intro term hterm
        exact hterms term (by simp [hterm])
      calc
        N • MsmSemantics.g2MathSum ((point, scalar) :: rest) =
            N • (scalar.val • AffineGroup.toMathlib G2Affine.curve point) +
              N • MsmSemantics.g2MathSum rest := by
                simp [MsmSemantics.g2MathSum, nsmul_add]
        _ = 0 := by rw [hscaled, hrest, add_zero]

theorem g1_output (terms : List MsmSemantics.G1ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g1Affine term.1.1 = true) :
    Subgroup.g1Affine (MsmSemantics.g1Value terms) = true := by
  apply (SubgroupSemantics.g1Affine_eq_true_iff_nsmul_zero
    ⟨MsmSemantics.g1Value terms, MsmSemantics.g1Value_onCurve terms⟩).2
  rw [MsmSemantics.g1_nsmul_sum]
  exact g1MathSum_nsmul_zero terms hterms

theorem g2_output (terms : List MsmSemantics.G2ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g2Affine term.1.1 = true) :
    Subgroup.g2Affine (MsmSemantics.g2Value terms) = true := by
  apply (SubgroupSemantics.g2Affine_eq_true_iff_nsmul_zero
    ⟨MsmSemantics.g2Value terms, MsmSemantics.g2Value_onCurve terms⟩).2
  rw [MsmSemantics.g2_nsmul_sum]
  exact g2MathSum_nsmul_zero terms hterms

theorem g1_wire_output (terms : List MsmSemantics.G1ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g1Affine term.1.1 = true) :
    Subgroup.g1 (G1Affine.toWire (MsmSemantics.g1Value terms)) = true := by
  simpa [Subgroup.g1] using g1_output terms hterms

theorem g2_wire_output (terms : List MsmSemantics.G2ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g2Affine term.1.1 = true) :
    Subgroup.g2 (G2Affine.toWire (MsmSemantics.g2Value terms)) = true := by
  simpa [Subgroup.g2] using g2_output terms hterms

/-- If every decoded G1 term is curve-valid and passes the prime-subgroup
predicate, the encoded naive-MSM output decodes through the subgroup codec. -/
theorem g1Wire_encoded_output (terms : List Msm.G1WireTerm)
    (hvalid : ∀ term ∈ terms, Codec.ValidG1 term.1)
    (hsubgroup : ∀ term ∈ terms, Subgroup.g1 term.1 = true) :
    Codec.decodeG1Subgroup (Codec.encodeG1 (Msm.g1Wire terms)) 0 =
      some (Msm.g1Wire terms) := by
  let validTerms := g1ValidTermsOfWire terms hvalid
  have haccepted : ∀ term ∈ validTerms,
      Subgroup.g1Affine term.1.1 = true :=
    g1ValidTermsOfWire_accepted terms hvalid hsubgroup
  have hout : Subgroup.g1 (Msm.g1Wire terms) = true := by
    rw [← g1Value_validTermsOfWire terms hvalid]
    exact g1_wire_output validTerms haccepted
  apply (Codec.decodeG1Subgroup_eq_some_iff _ _ _).2
  exact ⟨Codec.decodeG1_encodeG1 _ (Msm.g1Wire_valid terms hvalid), hout⟩

/-- If every decoded G2 term is curve-valid and passes the prime-subgroup
predicate, the encoded naive-MSM output decodes through the subgroup codec. -/
theorem g2Wire_encoded_output (terms : List Msm.G2WireTerm)
    (hvalid : ∀ term ∈ terms, Codec.ValidG2 term.1)
    (hsubgroup : ∀ term ∈ terms, Subgroup.g2 term.1 = true) :
    Codec.decodeG2Subgroup (Codec.encodeG2 (Msm.g2Wire terms)) 0 =
      some (Msm.g2Wire terms) := by
  let validTerms := g2ValidTermsOfWire terms hvalid
  have haccepted : ∀ term ∈ validTerms,
      Subgroup.g2Affine term.1.1 = true :=
    g2ValidTermsOfWire_accepted terms hvalid hsubgroup
  have hout : Subgroup.g2 (Msm.g2Wire terms) = true := by
    rw [← g2Value_validTermsOfWire terms hvalid]
    exact g2_wire_output validTerms haccepted
  apply (Codec.decodeG2Subgroup_eq_some_iff _ _ _).2
  exact ⟨Codec.decodeG2_encodeG2 _ (Msm.g2Wire_valid terms hvalid), hout⟩

end Challenge.Bls12381.ProofSupport.MsmSubgroup
