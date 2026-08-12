import Challenge.Bls12381.ProofSupport.ScalarMul

set_option warningAsError true

/-! # Shared naive multi-scalar multiplication

The executable boundary is a left fold of the approved proof-visible affine
addition and scalar multiplication.  Each scalar is an exact unreduced EIP
256-bit value; no silent truncation or subgroup-order reduction occurs here.
-/

namespace Challenge.Bls12381.ProofSupport.Msm

open EvmSemantics.Crypto.Bls12381

abbrev G1Term := G1Affine.Point × ScalarMul.Scalar256
abbrev G2Term := G2Affine.Point × ScalarMul.Scalar256
abbrev G1WireTerm := Point × ScalarMul.Scalar256
abbrev G2WireTerm := G2Point × ScalarMul.Scalar256

def g1TermOfWire (term : G1WireTerm) : G1Term :=
  (G1Affine.ofWire term.1, term.2)

def g2TermOfWire (term : G2WireTerm) : G2Term :=
  (G2Affine.ofWire term.1, term.2)

def foldG1 : G1Affine.Point → List G1Term →
    G1Affine.Point
  | acc, [] => acc
  | acc, (point, scalar) :: rest =>
      foldG1 (G1Affine.add acc (ScalarMul.g1Eip scalar point)) rest

def g1 (terms : List G1Term) : G1Affine.Point :=
  foldG1 G1Affine.infinity terms

def foldG2 : G2Affine.Point → List G2Term →
    G2Affine.Point
  | acc, [] => acc
  | acc, (point, scalar) :: rest =>
      foldG2 (G2Affine.add acc (ScalarMul.g2Eip scalar point)) rest

def g2 (terms : List G2Term) : G2Affine.Point :=
  foldG2 G2Affine.infinity terms

@[simp] theorem foldG1_nil (acc : G1Affine.Point) : foldG1 acc [] = acc := rfl

@[simp] theorem foldG1_cons (acc point : G1Affine.Point)
    (scalar : ScalarMul.Scalar256) (rest : List G1Term) :
    foldG1 acc ((point, scalar) :: rest) =
      foldG1 (G1Affine.add acc (ScalarMul.g1Eip scalar point)) rest := rfl

theorem foldG1_append (acc : G1Affine.Point)
    (left right : List G1Term) :
    foldG1 acc (left ++ right) = foldG1 (foldG1 acc left) right := by
  induction left generalizing acc with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨point, scalar⟩
      simp only [List.cons_append, foldG1_cons]
      exact ih _

@[simp] theorem foldG2_nil (acc : G2Affine.Point) : foldG2 acc [] = acc := rfl

@[simp] theorem foldG2_cons (acc point : G2Affine.Point)
    (scalar : ScalarMul.Scalar256) (rest : List G2Term) :
    foldG2 acc ((point, scalar) :: rest) =
      foldG2 (G2Affine.add acc (ScalarMul.g2Eip scalar point)) rest := rfl

theorem foldG2_append (acc : G2Affine.Point)
    (left right : List G2Term) :
    foldG2 acc (left ++ right) = foldG2 (foldG2 acc left) right := by
  induction left generalizing acc with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨point, scalar⟩
      simp only [List.cons_append, foldG2_cons]
      exact ih _

@[simp] theorem g1_nil : g1 [] = G1Affine.infinity := rfl

@[simp] theorem g2_nil : g2 [] = G2Affine.infinity := rfl

@[simp] theorem g1_single (point : G1Affine.Point)
    (scalar : ScalarMul.Scalar256) :
    g1 [(point, scalar)] = ScalarMul.g1Eip scalar point := by
  simp [g1, G1Affine.add]

@[simp] theorem g2_single (point : G2Affine.Point)
    (scalar : ScalarMul.Scalar256) :
    g2 [(point, scalar)] = ScalarMul.g2Eip scalar point := by
  simp [g2, G2Affine.add]

theorem g1_cons (point : G1Affine.Point) (scalar : ScalarMul.Scalar256)
    (rest : List G1Term) :
    g1 ((point, scalar) :: rest) =
      foldG1 (ScalarMul.g1Eip scalar point) rest := by
  simp [g1, G1Affine.add]

theorem g2_cons (point : G2Affine.Point) (scalar : ScalarMul.Scalar256)
    (rest : List G2Term) :
    g2 ((point, scalar) :: rest) =
      foldG2 (ScalarMul.g2Eip scalar point) rest := by
  simp [g2, G2Affine.add]

theorem g1_append (left right : List G1Term) :
    g1 (left ++ right) = foldG1 (g1 left) right := by
  exact foldG1_append G1Affine.infinity left right

theorem g2_append (left right : List G2Term) :
    g2 (left ++ right) = foldG2 (g2 left) right := by
  exact foldG2_append G2Affine.infinity left right

theorem foldG1_onCurve (acc : G1Affine.Point) (terms : List G1Term)
    (hacc : G1Affine.OnCurve acc)
    (hterms : ∀ term ∈ terms, G1Affine.OnCurve term.1) :
    G1Affine.OnCurve (foldG1 acc terms) := by
  induction terms generalizing acc with
  | nil => exact hacc
  | cons term rest ih =>
      rcases term with ⟨point, scalar⟩
      apply ih
      · exact G1Affine.onCurve_add acc (ScalarMul.g1Eip scalar point) hacc
          (ScalarMul.g1_onCurve scalar.val point
            (hterms (point, scalar) (by simp)))
      · intro term hterm
        exact hterms term (by simp [hterm])

theorem foldG2_onCurve (acc : G2Affine.Point) (terms : List G2Term)
    (hacc : G2Affine.OnCurve acc)
    (hterms : ∀ term ∈ terms, G2Affine.OnCurve term.1) :
    G2Affine.OnCurve (foldG2 acc terms) := by
  induction terms generalizing acc with
  | nil => exact hacc
  | cons term rest ih =>
      rcases term with ⟨point, scalar⟩
      apply ih
      · exact G2Affine.onCurve_add acc (ScalarMul.g2Eip scalar point) hacc
          (ScalarMul.g2_onCurve scalar.val point
            (hterms (point, scalar) (by simp)))
      · intro term hterm
        exact hterms term (by simp [hterm])

theorem g1_onCurve (terms : List G1Term)
    (hterms : ∀ term ∈ terms, G1Affine.OnCurve term.1) :
    G1Affine.OnCurve (g1 terms) :=
  foldG1_onCurve G1Affine.infinity terms
    (LawfulAffine.onCurve_infinity G1Affine.curve) hterms

theorem g2_onCurve (terms : List G2Term)
    (hterms : ∀ term ∈ terms, G2Affine.OnCurve term.1) :
    G2Affine.OnCurve (g2 terms) :=
  foldG2_onCurve G2Affine.infinity terms
    (LawfulAffine.onCurve_infinity G2Affine.curve) hterms

/-! ## Decoded-wire adapters -/

def g1Wire (terms : List G1WireTerm) : Point :=
  G1Affine.toWire (g1 (terms.map g1TermOfWire))

def g2Wire (terms : List G2WireTerm) : G2Point :=
  G2Affine.toWire (g2 (terms.map g2TermOfWire))

@[simp] theorem g1Wire_refines (terms : List G1WireTerm) :
    G1Affine.ofWire (g1Wire terms) = g1 (terms.map g1TermOfWire) := by
  simp [g1Wire]

@[simp] theorem g2Wire_refines (terms : List G2WireTerm) :
    G2Affine.ofWire (g2Wire terms) = g2 (terms.map g2TermOfWire) := by
  simp [g2Wire]

private theorem g1TermOfWire_onCurve (term : G1WireTerm)
    (hvalid : Codec.ValidG1 term.1) :
    G1Affine.OnCurve (g1TermOfWire term).1 := by
  rcases term with ⟨point, scalar⟩
  cases point with
  | infinity => exact LawfulAffine.onCurve_infinity G1Affine.curve
  | affine x y => exact G1Affine.onCurve_ofWire hvalid

private theorem g2TermOfWire_onCurve (term : G2WireTerm)
    (hvalid : Codec.ValidG2 term.1) :
    G2Affine.OnCurve (g2TermOfWire term).1 := by
  rcases term with ⟨point, scalar⟩
  cases point with
  | infinity => exact LawfulAffine.onCurve_infinity G2Affine.curve
  | affine x y => exact G2Affine.onCurve_ofWire hvalid

theorem g1Wire_valid (terms : List G1WireTerm)
    (hterms : ∀ term ∈ terms, Codec.ValidG1 term.1) :
    Codec.ValidG1 (g1Wire terms) := by
  have hmap : ∀ term ∈ terms.map g1TermOfWire,
      G1Affine.OnCurve term.1 := by
    intro term hterm
    obtain ⟨wireTerm, hwireTerm, rfl⟩ := List.mem_map.mp hterm
    exact g1TermOfWire_onCurve wireTerm (hterms wireTerm hwireTerm)
  have houtput := g1_onCurve (terms.map g1TermOfWire) hmap
  unfold g1Wire
  cases hresult : g1 (List.map g1TermOfWire terms) with
  | infinity => trivial
  | affine x y =>
      rw [hresult] at houtput
      exact G1Affine.onCurve_toWire houtput

theorem g2Wire_valid (terms : List G2WireTerm)
    (hterms : ∀ term ∈ terms, Codec.ValidG2 term.1) :
    Codec.ValidG2 (g2Wire terms) := by
  have hmap : ∀ term ∈ terms.map g2TermOfWire,
      G2Affine.OnCurve term.1 := by
    intro term hterm
    obtain ⟨wireTerm, hwireTerm, rfl⟩ := List.mem_map.mp hterm
    exact g2TermOfWire_onCurve wireTerm (hterms wireTerm hwireTerm)
  have houtput := g2_onCurve (terms.map g2TermOfWire) hmap
  unfold g2Wire
  cases hresult : g2 (List.map g2TermOfWire terms) with
  | infinity => trivial
  | affine x y =>
      rw [hresult] at houtput
      exact G2Affine.onCurve_toWire houtput

end Challenge.Bls12381.ProofSupport.Msm
