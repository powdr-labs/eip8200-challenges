import Challenge.Bls12381.ProofSupport.Msm
import Challenge.Bls12381.ProofSupport.AffineGroupBls
import Challenge.Bls12381.ProofSupport.ScalarMulSemantics

set_option warningAsError true

/-!
# Independent group semantics for naive MSM

This proof-only module maps the executable left folds into Mathlib's affine
elliptic-curve groups.  It is intentionally separate from `Msm`, so the
executable fold itself carries no additional group-model instrumentation.
-/

namespace Challenge.Bls12381.ProofSupport.MsmSemantics

abbrev G1ValidPoint := AffineGroup.Point G1Affine.curve
abbrev G2ValidPoint := AffineGroup.Point G2Affine.curve
abbrev G1ValidTerm := G1ValidPoint × ScalarMul.Scalar256
abbrev G2ValidTerm := G2ValidPoint × ScalarMul.Scalar256

def forgetG1Term (term : G1ValidTerm) : Msm.G1Term :=
  (term.1.1, term.2)

def forgetG2Term (term : G2ValidTerm) : Msm.G2Term :=
  (term.1.1, term.2)

def g1MathSum (terms : List G1ValidTerm) :
    (AffineGroup.mathCurve G1Affine.curve).toAffine.Point :=
  (terms.map fun term =>
    term.2.val • AffineGroup.toMathlib G1Affine.curve term.1).sum

def g2MathSum (terms : List G2ValidTerm) :
    (AffineGroup.mathCurve G2Affine.curve).toAffine.Point :=
  (terms.map fun term =>
    term.2.val • AffineGroup.toMathlib G2Affine.curve term.1).sum

private theorem forgetG1Terms_onCurve (terms : List G1ValidTerm) :
    ∀ term ∈ terms.map forgetG1Term, G1Affine.OnCurve term.1 := by
  intro term hterm
  obtain ⟨validTerm, _, rfl⟩ := List.mem_map.mp hterm
  exact validTerm.1.2

private theorem forgetG2Terms_onCurve (terms : List G2ValidTerm) :
    ∀ term ∈ terms.map forgetG2Term, G2Affine.OnCurve term.1 := by
  intro term hterm
  obtain ⟨validTerm, _, rfl⟩ := List.mem_map.mp hterm
  exact validTerm.1.2

def foldG1Valid (acc : G1ValidPoint) (terms : List G1ValidTerm) :
    G1ValidPoint :=
  ⟨Msm.foldG1 acc.1 (terms.map forgetG1Term),
    Msm.foldG1_onCurve acc.1 (terms.map forgetG1Term) acc.2
      (forgetG1Terms_onCurve terms)⟩

def foldG2Valid (acc : G2ValidPoint) (terms : List G2ValidTerm) :
    G2ValidPoint :=
  ⟨Msm.foldG2 acc.1 (terms.map forgetG2Term),
    Msm.foldG2_onCurve acc.1 (terms.map forgetG2Term) acc.2
      (forgetG2Terms_onCurve terms)⟩

def g1Valid (terms : List G1ValidTerm) : G1ValidPoint :=
  foldG1Valid (AffineGroup.infinity G1Affine.curve) terms

def g2Valid (terms : List G2ValidTerm) : G2ValidPoint :=
  foldG2Valid (AffineGroup.infinity G2Affine.curve) terms

def g1Value (terms : List G1ValidTerm) : G1Affine.Point :=
  (g1Valid terms).1

def g2Value (terms : List G2ValidTerm) : G2Affine.Point :=
  (g2Valid terms).1

theorem g1Value_onCurve (terms : List G1ValidTerm) :
    G1Affine.OnCurve (g1Value terms) := (g1Valid terms).2

theorem g2Value_onCurve (terms : List G2ValidTerm) :
    G2Affine.OnCurve (g2Value terms) := (g2Valid terms).2

theorem foldG1_nsmul_sum (acc : G1ValidPoint)
    (terms : List G1ValidTerm) :
    AffineGroup.toMathlib G1Affine.curve (foldG1Valid acc terms) =
      AffineGroup.toMathlib G1Affine.curve acc + g1MathSum terms := by
  induction terms generalizing acc with
  | nil =>
      have hfold : foldG1Valid acc [] = acc := by
        apply Subtype.ext
        rfl
      simp [g1MathSum, hfold]
  | cons term rest ih =>
      rcases term with ⟨point, scalar⟩
      let scalarPoint : G1ValidPoint :=
        ⟨ScalarMul.g1Eip scalar point.1,
          ScalarMul.g1_onCurve scalar.val point.1 point.2⟩
      let next : G1ValidPoint :=
        AffineGroup.add G1Affine.curve G1Affine.two_ne_zero acc scalarPoint
      have hnext : next.1 =
          G1Affine.add acc.1 (ScalarMul.g1Eip scalar point.1) := rfl
      have hfold : foldG1Valid acc ((point, scalar) :: rest) =
          foldG1Valid next rest := by
        apply Subtype.ext
        exact congrArg (fun nextPoint => Msm.foldG1 nextPoint
          (rest.map forgetG1Term)) hnext.symm
      calc
        AffineGroup.toMathlib G1Affine.curve
            (foldG1Valid acc ((point, scalar) :: rest)) =
            AffineGroup.toMathlib G1Affine.curve
              (foldG1Valid next rest) := congrArg _ hfold
        _ = AffineGroup.toMathlib G1Affine.curve next +
              g1MathSum rest := ih next
        _ = (AffineGroup.toMathlib G1Affine.curve acc +
              AffineGroup.toMathlib G1Affine.curve scalarPoint) +
              g1MathSum rest := by
                rw [AffineGroup.toMathlib_add]
        _ = (AffineGroup.toMathlib G1Affine.curve acc +
              scalar.val • AffineGroup.toMathlib G1Affine.curve point) +
              g1MathSum rest := by
                rw [show AffineGroup.toMathlib G1Affine.curve scalarPoint =
                    scalar.val • AffineGroup.toMathlib G1Affine.curve point by
                  exact ScalarMul.g1_nsmul scalar.val point.1 point.2]
        _ = AffineGroup.toMathlib G1Affine.curve acc +
              g1MathSum ((point, scalar) :: rest) := by
                simp [g1MathSum, add_assoc]

theorem foldG2_nsmul_sum (acc : G2ValidPoint)
    (terms : List G2ValidTerm) :
    AffineGroup.toMathlib G2Affine.curve (foldG2Valid acc terms) =
      AffineGroup.toMathlib G2Affine.curve acc + g2MathSum terms := by
  induction terms generalizing acc with
  | nil =>
      have hfold : foldG2Valid acc [] = acc := by
        apply Subtype.ext
        rfl
      simp [g2MathSum, hfold]
  | cons term rest ih =>
      rcases term with ⟨point, scalar⟩
      let scalarPoint : G2ValidPoint :=
        ⟨ScalarMul.g2Eip scalar point.1,
          ScalarMul.g2_onCurve scalar.val point.1 point.2⟩
      let next : G2ValidPoint :=
        AffineGroup.add G2Affine.curve G2Affine.two_ne_zero acc scalarPoint
      have hnext : next.1 =
          G2Affine.add acc.1 (ScalarMul.g2Eip scalar point.1) := rfl
      have hfold : foldG2Valid acc ((point, scalar) :: rest) =
          foldG2Valid next rest := by
        apply Subtype.ext
        exact congrArg (fun nextPoint => Msm.foldG2 nextPoint
          (rest.map forgetG2Term)) hnext.symm
      calc
        AffineGroup.toMathlib G2Affine.curve
            (foldG2Valid acc ((point, scalar) :: rest)) =
            AffineGroup.toMathlib G2Affine.curve
              (foldG2Valid next rest) := congrArg _ hfold
        _ = AffineGroup.toMathlib G2Affine.curve next +
              g2MathSum rest := ih next
        _ = (AffineGroup.toMathlib G2Affine.curve acc +
              AffineGroup.toMathlib G2Affine.curve scalarPoint) +
              g2MathSum rest := by
                rw [AffineGroup.toMathlib_add]
        _ = (AffineGroup.toMathlib G2Affine.curve acc +
              scalar.val • AffineGroup.toMathlib G2Affine.curve point) +
              g2MathSum rest := by
                rw [show AffineGroup.toMathlib G2Affine.curve scalarPoint =
                    scalar.val • AffineGroup.toMathlib G2Affine.curve point by
                  exact ScalarMul.g2_nsmul scalar.val point.1 point.2]
        _ = AffineGroup.toMathlib G2Affine.curve acc +
              g2MathSum ((point, scalar) :: rest) := by
                simp [g2MathSum, add_assoc]

theorem g1_nsmul_sum (terms : List G1ValidTerm) :
    AffineGroup.toMathlib G1Affine.curve
        ⟨g1Value terms, g1Value_onCurve terms⟩ = g1MathSum terms := by
  change AffineGroup.toMathlib G1Affine.curve (g1Valid terms) = _
  simpa [g1Valid] using
    foldG1_nsmul_sum (AffineGroup.infinity G1Affine.curve) terms

theorem g2_nsmul_sum (terms : List G2ValidTerm) :
    AffineGroup.toMathlib G2Affine.curve
        ⟨g2Value terms, g2Value_onCurve terms⟩ = g2MathSum terms := by
  change AffineGroup.toMathlib G2Affine.curve (g2Valid terms) = _
  simpa [g2Valid] using
    foldG2_nsmul_sum (AffineGroup.infinity G2Affine.curve) terms

end Challenge.Bls12381.ProofSupport.MsmSemantics
