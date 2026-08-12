import Challenge.Bls12381.ProofSupport.G1Affine

set_option warningAsError true

namespace Checks.Bls12381G1Affine

open Challenge.Bls12381.ProofSupport

example (point : EvmSemantics.Crypto.Bls12381.Point) :
    G1Affine.toWire (G1Affine.ofWire point) = point :=
  G1Affine.toWire_ofWire point

example (point : G1Affine.Point) :
    G1Affine.OnCurve point -> G1Affine.OnCurve (G1Affine.double point) :=
  G1Affine.onCurve_double point

example (left right : G1Affine.Point) :
    G1Affine.OnCurve left -> G1Affine.OnCurve right ->
      G1Affine.OnCurve (G1Affine.add left right) :=
  G1Affine.onCurve_add left right

example (x y : EvmSemantics.Crypto.Bls12381.Fp)
    (hcurve : EvmSemantics.Crypto.Bls12381.onCurve x y = true) :
    G1Affine.OnCurve (G1Affine.ofWire (.affine x y)) :=
  G1Affine.onCurve_ofWire hcurve

example (x y : G1Affine.Field)
    (hcurve : G1Affine.OnCurve (.affine x y)) :
    EvmSemantics.Crypto.Bls12381.onCurve
      (PrimeField.finEquiv.symm x) (PrimeField.finEquiv.symm y) = true :=
  G1Affine.onCurve_toWire hcurve

/--
info: 'Challenge.Bls12381.ProofSupport.G1Affine.toWire_ofWire' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms G1Affine.toWire_ofWire

/--
info: 'Challenge.Bls12381.ProofSupport.G1Affine.onCurve_ofWire' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms G1Affine.onCurve_ofWire

/--
info: 'Challenge.Bls12381.ProofSupport.G1Affine.onCurve_toWire' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms G1Affine.onCurve_toWire

/--
info: 'Challenge.Bls12381.ProofSupport.G1Affine.onCurve_double' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms G1Affine.onCurve_double

/--
info: 'Challenge.Bls12381.ProofSupport.G1Affine.onCurve_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms G1Affine.onCurve_add

/--
info: 'Challenge.Bls12381.ProofSupport.G1Affine.ofWire_toWire' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms G1Affine.ofWire_toWire

/--
info: 'Challenge.Bls12381.ProofSupport.G1Affine.two_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms G1Affine.two_ne_zero

end Checks.Bls12381G1Affine
