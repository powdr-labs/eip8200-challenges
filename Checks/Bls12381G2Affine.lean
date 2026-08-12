import Challenge.Bls12381.ProofSupport.G2Affine

set_option warningAsError true

namespace Checks.Bls12381G2Affine

open Challenge.Bls12381.ProofSupport

example (point : EvmSemantics.Crypto.Bls12381.G2Point) :
    G2Affine.toWire (G2Affine.ofWire point) = point :=
  G2Affine.toWire_ofWire point

example (point : G2Affine.Point) :
    G2Affine.OnCurve point -> G2Affine.OnCurve (G2Affine.double point) :=
  G2Affine.onCurve_double point

example (left right : G2Affine.Point) :
    G2Affine.OnCurve left -> G2Affine.OnCurve right ->
      G2Affine.OnCurve (G2Affine.add left right) :=
  G2Affine.onCurve_add left right

example (x y : EvmSemantics.Crypto.Bls12381.Fp2)
    (hcurve : EvmSemantics.Crypto.G2.onCurve
      EvmSemantics.Crypto.Bls12381.g2Curve x y = true) :
    G2Affine.OnCurve (G2Affine.ofWire (.affine x y)) :=
  G2Affine.onCurve_ofWire hcurve

example (x y : G2Affine.Field)
    (hcurve : G2Affine.OnCurve (.affine x y)) :
    EvmSemantics.Crypto.G2.onCurve EvmSemantics.Crypto.Bls12381.g2Curve
      (LawfulFp2.toWire x) (LawfulFp2.toWire y) = true :=
  G2Affine.onCurve_toWire hcurve

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulFp2.ofWire_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LawfulFp2.ofWire_add

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulFp2.ofWire_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LawfulFp2.ofWire_mul

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulFp2.ofWire_square' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LawfulFp2.ofWire_square

/--
info: 'Challenge.Bls12381.ProofSupport.LawfulFp2.ofWire_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LawfulFp2.ofWire_injective

/--
info: 'Challenge.Bls12381.ProofSupport.G2Affine.toWire_ofWire' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms G2Affine.toWire_ofWire

/--
info: 'Challenge.Bls12381.ProofSupport.G2Affine.onCurve_ofWire' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms G2Affine.onCurve_ofWire

/--
info: 'Challenge.Bls12381.ProofSupport.G2Affine.onCurve_toWire' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms G2Affine.onCurve_toWire

/--
info: 'Challenge.Bls12381.ProofSupport.G2Affine.onCurve_double' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms G2Affine.onCurve_double

/--
info: 'Challenge.Bls12381.ProofSupport.G2Affine.onCurve_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms G2Affine.onCurve_add

/--
info: 'Challenge.Bls12381.ProofSupport.G2Affine.ofWire_toWire' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms G2Affine.ofWire_toWire

/--
info: 'Challenge.Bls12381.ProofSupport.G2Affine.two_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms G2Affine.two_ne_zero

end Checks.Bls12381G2Affine
