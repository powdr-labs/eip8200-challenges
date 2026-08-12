import Challenge.Bls12381.ProofSupport.Msm

set_option warningAsError true

namespace Checks.Bls12381Msm

open Challenge.Bls12381.ProofSupport

example (acc : G1Affine.Point)
    (left right : List (G1Affine.Point × ScalarMul.Scalar256)) :
    Msm.foldG1 acc (left ++ right) = Msm.foldG1 (Msm.foldG1 acc left) right :=
  Msm.foldG1_append acc left right

example (acc : G2Affine.Point)
    (left right : List (G2Affine.Point × ScalarMul.Scalar256)) :
    Msm.foldG2 acc (left ++ right) = Msm.foldG2 (Msm.foldG2 acc left) right :=
  Msm.foldG2_append acc left right

example : Msm.g1 [] = G1Affine.infinity := Msm.g1_nil

example : Msm.g2 [] = G2Affine.infinity := Msm.g2_nil

example (point : G1Affine.Point) (scalar : ScalarMul.Scalar256) :
    Msm.g1 [(point, scalar)] = ScalarMul.g1Eip scalar point :=
  Msm.g1_single point scalar

example (point : G2Affine.Point) (scalar : ScalarMul.Scalar256) :
    Msm.g2 [(point, scalar)] = ScalarMul.g2Eip scalar point :=
  Msm.g2_single point scalar

example (point : G1Affine.Point) (scalar : ScalarMul.Scalar256)
    (rest : List Msm.G1Term) :
    Msm.g1 ((point, scalar) :: rest) =
      Msm.foldG1 (ScalarMul.g1Eip scalar point) rest :=
  Msm.g1_cons point scalar rest

example (point : G2Affine.Point) (scalar : ScalarMul.Scalar256)
    (rest : List Msm.G2Term) :
    Msm.g2 ((point, scalar) :: rest) =
      Msm.foldG2 (ScalarMul.g2Eip scalar point) rest :=
  Msm.g2_cons point scalar rest

example (left right : List Msm.G1Term) :
    Msm.g1 (left ++ right) = Msm.foldG1 (Msm.g1 left) right :=
  Msm.g1_append left right

example (left right : List Msm.G2Term) :
    Msm.g2 (left ++ right) = Msm.foldG2 (Msm.g2 left) right :=
  Msm.g2_append left right

example (terms : List (G1Affine.Point × ScalarMul.Scalar256))
    (hterms : ∀ term ∈ terms, G1Affine.OnCurve term.1) :
    G1Affine.OnCurve (Msm.g1 terms) := Msm.g1_onCurve terms hterms

example (terms : List (G2Affine.Point × ScalarMul.Scalar256))
    (hterms : ∀ term ∈ terms, G2Affine.OnCurve term.1) :
    G2Affine.OnCurve (Msm.g2 terms) := Msm.g2_onCurve terms hterms

example (terms : List Msm.G1WireTerm) :
    G1Affine.ofWire (Msm.g1Wire terms) =
      Msm.g1 (terms.map Msm.g1TermOfWire) :=
  Msm.g1Wire_refines terms

example (terms : List Msm.G2WireTerm) :
    G2Affine.ofWire (Msm.g2Wire terms) =
      Msm.g2 (terms.map Msm.g2TermOfWire) :=
  Msm.g2Wire_refines terms

example (terms : List Msm.G1WireTerm)
    (hterms : ∀ term ∈ terms, Codec.ValidG1 term.1) :
    Codec.ValidG1 (Msm.g1Wire terms) := Msm.g1Wire_valid terms hterms

example (terms : List Msm.G2WireTerm)
    (hterms : ∀ term ∈ terms, Codec.ValidG2 term.1) :
    Codec.ValidG2 (Msm.g2Wire terms) := Msm.g2Wire_valid terms hterms

/--
info: 'Challenge.Bls12381.ProofSupport.Msm.foldG1_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Msm.foldG1_nil

/--
info: 'Challenge.Bls12381.ProofSupport.Msm.foldG1_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Msm.foldG1_cons

/--
info: 'Challenge.Bls12381.ProofSupport.Msm.foldG1_append' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Msm.foldG1_append

/--
info: 'Challenge.Bls12381.ProofSupport.Msm.foldG2_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Msm.foldG2_nil

/--
info: 'Challenge.Bls12381.ProofSupport.Msm.foldG2_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Msm.foldG2_cons

/--
info: 'Challenge.Bls12381.ProofSupport.Msm.foldG2_append' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Msm.foldG2_append

/-- info: 'Challenge.Bls12381.ProofSupport.Msm.g1_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Msm.g1_nil

/-- info: 'Challenge.Bls12381.ProofSupport.Msm.g2_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Msm.g2_nil

/-- info: 'Challenge.Bls12381.ProofSupport.Msm.g1_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Msm.g1_single

/-- info: 'Challenge.Bls12381.ProofSupport.Msm.g2_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Msm.g2_single

/-- info: 'Challenge.Bls12381.ProofSupport.Msm.g1_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Msm.g1_cons

/-- info: 'Challenge.Bls12381.ProofSupport.Msm.g2_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Msm.g2_cons

/-- info: 'Challenge.Bls12381.ProofSupport.Msm.g1_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Msm.g1_append

/-- info: 'Challenge.Bls12381.ProofSupport.Msm.g2_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Msm.g2_append

/-- info: 'Challenge.Bls12381.ProofSupport.Msm.foldG1_onCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Msm.foldG1_onCurve

/-- info: 'Challenge.Bls12381.ProofSupport.Msm.foldG2_onCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Msm.foldG2_onCurve

/-- info: 'Challenge.Bls12381.ProofSupport.Msm.g1_onCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Msm.g1_onCurve

/-- info: 'Challenge.Bls12381.ProofSupport.Msm.g2_onCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Msm.g2_onCurve

/-- info: 'Challenge.Bls12381.ProofSupport.Msm.g1Wire_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Msm.g1Wire_refines

/-- info: 'Challenge.Bls12381.ProofSupport.Msm.g2Wire_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Msm.g2Wire_refines

/-- info: 'Challenge.Bls12381.ProofSupport.Msm.g1Wire_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Msm.g1Wire_valid

/-- info: 'Challenge.Bls12381.ProofSupport.Msm.g2Wire_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Msm.g2Wire_valid

end Checks.Bls12381Msm
