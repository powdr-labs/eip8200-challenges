import Challenge.Bls12381.ProofSupport.MsmSubgroup

set_option warningAsError true

namespace Checks.Bls12381MsmSubgroup

open Challenge.Bls12381.ProofSupport

example (terms : List MsmSemantics.G1ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g1Affine term.1.1 = true) :
    Subgroup.g1Affine (MsmSemantics.g1Value terms) = true :=
  MsmSubgroup.g1_output terms hterms

example (terms : List MsmSemantics.G2ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g2Affine term.1.1 = true) :
    Subgroup.g2Affine (MsmSemantics.g2Value terms) = true :=
  MsmSubgroup.g2_output terms hterms

example (terms : List MsmSemantics.G1ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g1Affine term.1.1 = true) :
    Subgroup.g1 (G1Affine.toWire (MsmSemantics.g1Value terms)) = true :=
  MsmSubgroup.g1_wire_output terms hterms

example (terms : List MsmSemantics.G2ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g2Affine term.1.1 = true) :
    Subgroup.g2 (G2Affine.toWire (MsmSemantics.g2Value terms)) = true :=
  MsmSubgroup.g2_wire_output terms hterms

example (terms : List Msm.G1WireTerm)
    (hvalid : ∀ term ∈ terms, Codec.ValidG1 term.1)
    (hsubgroup : ∀ term ∈ terms, Subgroup.g1 term.1 = true) :
    Codec.decodeG1Subgroup (Codec.encodeG1 (Msm.g1Wire terms)) 0 =
      some (Msm.g1Wire terms) :=
  MsmSubgroup.g1Wire_encoded_output terms hvalid hsubgroup

example (terms : List Msm.G2WireTerm)
    (hvalid : ∀ term ∈ terms, Codec.ValidG2 term.1)
    (hsubgroup : ∀ term ∈ terms, Subgroup.g2 term.1 = true) :
    Codec.decodeG2Subgroup (Codec.encodeG2 (Msm.g2Wire terms)) 0 =
      some (Msm.g2Wire terms) :=
  MsmSubgroup.g2Wire_encoded_output terms hvalid hsubgroup

/-- info: 'Challenge.Bls12381.ProofSupport.MsmSubgroup.g1Wire_encoded_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MsmSubgroup.g1Wire_encoded_output

/-- info: 'Challenge.Bls12381.ProofSupport.MsmSubgroup.g2Wire_encoded_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MsmSubgroup.g2Wire_encoded_output

/--
info: 'Challenge.Bls12381.ProofSupport.MsmSubgroup.g1MathSum_nsmul_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MsmSubgroup.g1MathSum_nsmul_zero

/--
info: 'Challenge.Bls12381.ProofSupport.MsmSubgroup.g2MathSum_nsmul_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MsmSubgroup.g2MathSum_nsmul_zero

/-- info: 'Challenge.Bls12381.ProofSupport.MsmSubgroup.g1_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MsmSubgroup.g1_output

/-- info: 'Challenge.Bls12381.ProofSupport.MsmSubgroup.g2_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MsmSubgroup.g2_output

/-- info: 'Challenge.Bls12381.ProofSupport.MsmSubgroup.g1_wire_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MsmSubgroup.g1_wire_output

/-- info: 'Challenge.Bls12381.ProofSupport.MsmSubgroup.g2_wire_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MsmSubgroup.g2_wire_output

end Checks.Bls12381MsmSubgroup
