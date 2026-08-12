import Challenge.Bls12381.ProofSupport.ScalarMul
import Challenge.Bls12381.ProofSupport.ScalarMulSemantics

set_option warningAsError true

namespace Checks.Bls12381ScalarMul

open Challenge.Bls12381.ProofSupport

variable {P : Type} (zero : P) (add : P → P → P) (double : P → P)

example {Q : Type} [AddCommMonoid Q] (mapPoint : P → Q)
    (hzero : mapPoint zero = 0)
    (hadd : ∀ left right, mapPoint (add left right) =
      mapPoint left + mapPoint right)
    (hdouble : ∀ point, mapPoint (double point) =
      mapPoint point + mapPoint point)
    (scalar : Nat) (point : P) :
    mapPoint (ScalarMul.binary zero add double scalar point) =
      scalar • mapPoint point :=
  ScalarMul.binary_map_nsmul zero add double mapPoint
    hzero hadd hdouble scalar point

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.binary_map_nsmul' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.binary_map_nsmul

example (point : P) : ScalarMul.binary zero add double 0 point = zero :=
  ScalarMul.binary_zero zero add double point

example (point : P) : ScalarMul.binary zero add double 1 point = point :=
  ScalarMul.binary_one zero add double point

example (scalar : Nat) (point : P) :
    ScalarMul.binary zero add double (2 * scalar) point =
      ScalarMul.binary zero add double scalar (double point) :=
  ScalarMul.binary_even zero add double scalar point

example (scalar : Nat) (point : P) :
    ScalarMul.binary zero add double (2 * scalar + 1) point =
      if scalar = 0 then point
      else add (ScalarMul.binary zero add double scalar (double point)) point :=
  ScalarMul.binary_odd zero add double scalar point

example (scalar : Nat) (point : P) (hscalar : scalar ≠ 0) :
    ScalarMul.binary zero add double scalar point =
      if scalar = 1 then point
      else if scalar % 2 = 1 then
          add (ScalarMul.binary zero add double (scalar / 2) (double point)) point
        else ScalarMul.binary zero add double (scalar / 2) (double point) :=
  ScalarMul.binary_step zero add double scalar point hscalar

private def auditNatAdd (left right : Nat) : Nat := left + right

private def auditNatDouble (point : Nat) : Nat := 2 * point

/- The direct and audit interpreters execute one authoritative scalar program. -/
example (scalar point : Nat) :
    (ScalarMul.Program.audit 0 auditNatAdd auditNatDouble scalar point).value =
      ScalarMul.binary 0 auditNatAdd auditNatDouble scalar point :=
  ScalarMul.Program.audit_value 0 auditNatAdd auditNatDouble scalar point

/- Zero and one invoke no curve operations.  Two invokes only the initial
double, while three invokes that double followed by the odd addition. -/
#guard (ScalarMul.Program.audit 0 auditNatAdd auditNatDouble 0 7).events == []
#guard (ScalarMul.Program.audit 0 auditNatAdd auditNatDouble 1 7).events == []
#guard (ScalarMul.Program.audit 0 auditNatAdd auditNatDouble 2 7).events ==
  [.double]
#guard (ScalarMul.Program.audit 0 auditNatAdd auditNatDouble 3 7).events ==
  [.double, .add]

example (point : P) :
    (ScalarMul.Program.audit zero add double 0 point).events = [] :=
  ScalarMul.Program.audit_zero_events zero add double point

example (point : P) :
    (ScalarMul.Program.audit zero add double 1 point).events = [] :=
  ScalarMul.Program.audit_one_events zero add double point

example (point : P) :
    (ScalarMul.Program.audit zero add double 2 point).events = [.double] :=
  ScalarMul.Program.audit_two_events zero add double point

example (point : P) :
    (ScalarMul.Program.audit zero add double 3 point).events =
      [.double, .add] :=
  ScalarMul.Program.audit_three_events zero add double point

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.Program.audit_value' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.Program.audit_value

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.Program.runWith_direct_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.Program.runWith_direct_zero

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.Program.runWith_direct_one' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.Program.runWith_direct_one

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.Program.runWith_direct_step' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.Program.runWith_direct_step

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.Program.audit_zero_events' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.Program.audit_zero_events

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.Program.audit_one_events' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.Program.audit_one_events

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.Program.audit_two_events' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.Program.audit_two_events

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.Program.audit_three_events' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.Program.audit_three_events

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.binary_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.binary_zero

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.binary_one' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.binary_one

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.binary_step' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.binary_step

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.binary_even' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.binary_even

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.binary_odd' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.binary_odd

example (Valid : P → Prop)
    (hzero : Valid zero)
    (hadd : ∀ left right, Valid left → Valid right → Valid (add left right))
    (hdouble : ∀ point, Valid point → Valid (double point))
    (scalar : Nat) (point : P) (hpoint : Valid point) :
    Valid (ScalarMul.binary zero add double scalar point) :=
  ScalarMul.binary_preserves zero add double Valid hzero hadd hdouble scalar point hpoint

example (Valid : P → Prop)
    (hzero : Valid zero)
    (hadd : ∀ left right, Valid left → Valid right → Valid (add left right))
    (hdouble : ∀ point, Valid point → Valid (double point))
    (scalar : Nat) (point : P) (hpoint : Valid point) :
    (ScalarMul.binary (⟨zero, hzero⟩ : { point // Valid point })
      (fun (left right : { point // Valid point }) => ⟨add left.1 right.1,
        hadd left.1 right.1 left.2 right.2⟩)
      (fun (lifted : { point // Valid point }) =>
        ⟨double lifted.1, hdouble lifted.1 lifted.2⟩)
      scalar (⟨point, hpoint⟩ : { point // Valid point })).1 =
      ScalarMul.binary zero add double scalar point :=
  ScalarMul.binary_lift_val zero add double Valid hzero hadd hdouble
    scalar point hpoint

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.binary_lift_val' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.binary_lift_val

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.binary_preserves' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.binary_preserves

example {input : ByteArray} {offset scalar : Nat}
    (hdecode : Codec.decodeScalar input offset = some scalar) :
    (ScalarMul.scalar256OfDecode hdecode).val = scalar :=
  ScalarMul.scalar256OfDecode_val hdecode

example {input : ByteArray} {offset scalar : Nat}
    (hdecode : Codec.decodeScalar input offset = some scalar)
    (point : G1Affine.Point) :
    ScalarMul.g1Eip (ScalarMul.scalar256OfDecode hdecode) point =
      ScalarMul.g1 scalar point :=
  ScalarMul.g1Eip_of_decode hdecode point

example {input : ByteArray} {offset scalar : Nat}
    (hdecode : Codec.decodeScalar input offset = some scalar)
    (point : G2Affine.Point) :
    ScalarMul.g2Eip (ScalarMul.scalar256OfDecode hdecode) point =
      ScalarMul.g2 scalar point :=
  ScalarMul.g2Eip_of_decode hdecode point

example (point : G1Affine.Point) :
    ScalarMul.g1 0 point = G1Affine.infinity := ScalarMul.g1_zero point
example (point : G1Affine.Point) : ScalarMul.g1 1 point = point :=
  ScalarMul.g1_one point
example (point : G2Affine.Point) :
    ScalarMul.g2 0 point = G2Affine.infinity := ScalarMul.g2_zero point
example (point : G2Affine.Point) : ScalarMul.g2 1 point = point :=
  ScalarMul.g2_one point

example (scalar : Nat) (point : G1Affine.Point) :
    ScalarMul.g1 (2 * scalar) point =
      ScalarMul.g1 scalar (G1Affine.double point) :=
  ScalarMul.g1_even scalar point

example (scalar : Nat) (point : G2Affine.Point) :
    ScalarMul.g2 (2 * scalar + 1) point =
      G2Affine.add (ScalarMul.g2 scalar (G2Affine.double point)) point :=
  ScalarMul.g2_odd scalar point

example (scalar : Nat) (point : G1Affine.Point)
    (hpoint : G1Affine.OnCurve point) :
    G1Affine.OnCurve (ScalarMul.g1 scalar point) :=
  ScalarMul.g1_onCurve scalar point hpoint

example (scalar : Nat) (point : G2Affine.Point)
    (hpoint : G2Affine.OnCurve point) :
    G2Affine.OnCurve (ScalarMul.g2 scalar point) :=
  ScalarMul.g2_onCurve scalar point hpoint

example (scalar : Nat) (point : G1Affine.Point)
    (hpoint : G1Affine.OnCurve point) :
    AffineGroup.toMathlib G1Affine.curve
        ⟨ScalarMul.g1 scalar point,
          ScalarMul.g1_onCurve scalar point hpoint⟩ =
      scalar • AffineGroup.toMathlib G1Affine.curve ⟨point, hpoint⟩ :=
  ScalarMul.g1_nsmul scalar point hpoint

example (scalar : Nat) (point : G2Affine.Point)
    (hpoint : G2Affine.OnCurve point) :
    AffineGroup.toMathlib G2Affine.curve
        ⟨ScalarMul.g2 scalar point,
          ScalarMul.g2_onCurve scalar point hpoint⟩ =
      scalar • AffineGroup.toMathlib G2Affine.curve ⟨point, hpoint⟩ :=
  ScalarMul.g2_nsmul scalar point hpoint

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.binary_onCurve_nsmul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.binary_onCurve_nsmul

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g1_nsmul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g1_nsmul

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g2_nsmul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g2_nsmul

example (scalar : Nat) (point : EvmSemantics.Crypto.Bls12381.Point) :
    G1Affine.ofWire (ScalarMul.g1Wire scalar point) =
      ScalarMul.g1 scalar (G1Affine.ofWire point) :=
  ScalarMul.g1Wire_refines scalar point

example (scalar : Nat) (point : EvmSemantics.Crypto.Bls12381.G2Point) :
    G2Affine.ofWire (ScalarMul.g2Wire scalar point) =
      ScalarMul.g2 scalar (G2Affine.ofWire point) :=
  ScalarMul.g2Wire_refines scalar point

example (scalar : Nat) : ScalarMul.g1 scalar G1Affine.infinity =
    G1Affine.infinity := ScalarMul.g1_infinity scalar

example (scalar : Nat) : ScalarMul.g2 scalar G2Affine.infinity =
    G2Affine.infinity := ScalarMul.g2_infinity scalar

example (scalar : Nat) (point : EvmSemantics.Crypto.Bls12381.Point)
    (hpoint : Codec.ValidG1 point) :
    Codec.ValidG1 (ScalarMul.g1Wire scalar point) :=
  ScalarMul.g1Wire_valid scalar point hpoint

example (scalar : Nat) (point : EvmSemantics.Crypto.Bls12381.G2Point)
    (hpoint : Codec.ValidG2 point) :
    Codec.ValidG2 (ScalarMul.g2Wire scalar point) :=
  ScalarMul.g2Wire_valid scalar point hpoint

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.scalar256OfDecode_val' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.scalar256OfDecode_val

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g1_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g1_zero

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g2_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g2_zero

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g1_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g1_one

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g2_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g2_one

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g1_even' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g1_even

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g2_even' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g2_even

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g1_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g1_odd

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g2_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g2_odd

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g1_onCurve' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g1_onCurve

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g2_onCurve' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g2_onCurve

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g1Wire_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g1Wire_refines

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g2Wire_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g2Wire_refines

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g1_infinity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g1_infinity

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g2_infinity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g2_infinity

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g1Wire_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g1Wire_valid

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g2Wire_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g2Wire_valid

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g1Eip_of_decode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g1Eip_of_decode

/--
info: 'Challenge.Bls12381.ProofSupport.ScalarMul.g2Eip_of_decode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ScalarMul.g2Eip_of_decode

end Checks.Bls12381ScalarMul
