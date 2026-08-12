import Challenge.Bls12381.ProofSupport.G1Projective

set_option warningAsError true

namespace Checks.Bls12381G1Projective

open Challenge.Bls12381.ProofSupport.G1Projective

example (point : EvmSemantics.Crypto.Bls12381.Point) :
    toWire (ofWire point) = point := toWire_ofWire point

#print axioms toWire_ofWire

example (point : Point) : add infinity point = point := infinity_add point
example (point : Point) (hz : point.z ≠ 0) : add point infinity = point :=
  add_infinity_of_z_ne_zero point hz
example (point : Point) (hz : point.z = 0) : double point = infinity :=
  double_of_z_eq_zero point hz
example (point : Point) (hy : point.y = 0) : double point = infinity :=
  double_of_y_eq_zero point hy

#print axioms infinity_add
#print axioms add_infinity_of_z_ne_zero
#print axioms double_of_y_eq_zero

end Checks.Bls12381G1Projective
