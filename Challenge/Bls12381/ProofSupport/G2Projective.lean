import Challenge.Bls12381.ProofSupport.LawfulFp2

set_option warningAsError true

/-! Projective G2 representation and its affine semantic boundary. -/

namespace Challenge.Bls12381.ProofSupport.G2Projective

open EvmSemantics.Crypto.Bls12381

structure Point where
  x : LawfulFp2.Carrier
  y : LawfulFp2.Carrier
  z : LawfulFp2.Carrier
deriving DecidableEq

def infinity : Point := { x := 0, y := 1, z := 0 }

/-- Embed the pinned affine Fp2 wire carrier into lawful Jacobian
coordinates. -/
def ofWire : EvmSemantics.Crypto.Bls12381.G2Point → Point
  | .infinity => infinity
  | .affine x y =>
      { x := LawfulFp2.ofWire x, y := LawfulFp2.ofWire y, z := 1 }

/-- Convert lawful Jacobian coordinates back to the pinned affine Fp2 wire
carrier using the certified lawful field inverse. -/
def toWire (point : Point) : EvmSemantics.Crypto.Bls12381.G2Point :=
  if point.z = 0 then .infinity
  else if point.z = 1 then
    .affine (LawfulFp2.toWire point.x) (LawfulFp2.toWire point.y)
  else
    let zInv := point.z⁻¹
    .affine (LawfulFp2.toWire (point.x * zInv ^ 2))
      (LawfulFp2.toWire (point.y * zInv ^ 3))

abbrev affine := ofWire
abbrev toAffine := toWire

@[simp] theorem infinity_toAffine : toAffine infinity = .infinity := by
  simp [toAffine, toWire, infinity]

@[simp] theorem affine_toAffine (point : EvmSemantics.Crypto.Bls12381.G2Point) :
    toAffine (affine point) = point := by
  cases point <;> simp [affine, toAffine, ofWire, toWire, infinity]

@[simp] theorem toWire_ofWire (point : EvmSemantics.Crypto.Bls12381.G2Point) :
    toWire (ofWire point) = point := affine_toAffine point

/-- Jacobian doubling for the `a = 0` BLS12-381 G2 twist. -/
def double (point : Point) : Point :=
  if point.z = 0 ∨ point.y = 0 then infinity
  else
    let a := point.x ^ 2
    let b := point.y ^ 2
    let c := b ^ 2
    let d := 2 * ((point.x + b) ^ 2 - a - c)
    let e := 3 * a
    let f := e ^ 2
    { x := f - 2 * d
      y := e * (d - (f - 2 * d)) - 8 * c
      z := 2 * point.y * point.z }

/-- Standard inversion-free Jacobian addition for G2, with all exceptional
branches handled before the generic formula. -/
def add (left right : Point) : Point :=
  if left.z = 0 then right
  else if right.z = 0 then left
  else
    let z1z1 := left.z ^ 2
    let z2z2 := right.z ^ 2
    let u1 := left.x * z2z2
    let u2 := right.x * z1z1
    let s1 := left.y * right.z * z2z2
    let s2 := right.y * left.z * z1z1
    if u1 = u2 then
      if s1 = s2 then double left else infinity
    else
      let h := u2 - u1
      let i := (2 * h) ^ 2
      let j := h * i
      let r := 2 * (s2 - s1)
      let v := u1 * i
      { x := r ^ 2 - j - 2 * v
        y := r * (v - (r ^ 2 - j - 2 * v)) - 2 * s1 * j
        z := ((left.z + right.z) ^ 2 - z1z1 - z2z2) * h }

@[simp] theorem double_infinity : double infinity = infinity := by
  simp [double, infinity]

@[simp] theorem double_of_z_eq_zero (point : Point) (hz : point.z = 0) :
    double point = infinity := by
  simp [double, hz]

@[simp] theorem double_of_y_eq_zero (point : Point) (hy : point.y = 0) :
    double point = infinity := by
  simp [double, hy]

@[simp] theorem infinity_add (point : Point) : add infinity point = point := by
  simp [add, infinity]

@[simp] theorem add_infinity_of_z_ne_zero (point : Point) (hz : point.z ≠ 0) :
    add point infinity = point := by
  simp [add, infinity, hz]

@[simp] theorem add_infinity_of_z_eq_zero (point : Point) (hz : point.z = 0) :
    add point infinity = infinity := by
  simp [add, infinity, hz]

end Challenge.Bls12381.ProofSupport.G2Projective
