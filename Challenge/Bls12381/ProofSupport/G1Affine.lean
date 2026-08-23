import Challenge.Bls12381.ProofSupport.LawfulAffine
import Challenge.Bls12381.ProofSupport.PrimeCertificate

set_option warningAsError true

/-! # Lawful affine BLS12-381 G1 boundary -/

namespace Challenge.Bls12381.ProofSupport.G1Affine

open EvmSemantics.Crypto.Bls12381

abbrev Field := PrimeField.LawfulFp
abbrev Point := LawfulAffine.Point Field

/-- The lawful `y² = x³ + 4` G1 curve. -/
def curve : LawfulAffine.Curve Field := { a := 0, b := 4 }

abbrev infinity : Point := .infinity
abbrev OnCurve : Point → Prop := LawfulAffine.OnCurve curve

def neg : Point → Point := LawfulAffine.neg
def double : Point → Point := LawfulAffine.double curve
def add : Point → Point → Point := LawfulAffine.add curve

/-- Inverse-free conversion from the decoded EIP wire carrier. -/
def ofWire : EvmSemantics.Crypto.Bls12381.Point → Point
  | .infinity => .infinity
  | .affine x y => .affine (PrimeField.finEquiv x) (PrimeField.finEquiv y)

/-- Inverse-free conversion back to the decoded EIP wire carrier. -/
def toWire : Point → EvmSemantics.Crypto.Bls12381.Point
  | .infinity => .infinity
  | .affine x y =>
      .affine (PrimeField.finEquiv.symm x) (PrimeField.finEquiv.symm y)

@[simp] theorem toWire_ofWire (point : EvmSemantics.Crypto.Bls12381.Point) :
    toWire (ofWire point) = point := by
  cases point <;> simp [toWire, ofWire]

@[simp] theorem ofWire_toWire (point : Point) :
    ofWire (toWire point) = point := by
  cases point <;> simp [toWire, ofWire]

theorem two_ne_zero : (2 : Field) ≠ 0 := by
  change ((2 : Nat) : ZMod p) ≠ 0
  intro hzero
  have hdiv : p ∣ 2 :=
    (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hzero
  norm_num [p, absU] at hdiv

theorem onCurve_double (point : Point) :
    OnCurve point → OnCurve (double point) :=
  LawfulAffine.onCurve_double curve point two_ne_zero

theorem onCurve_add (left right : Point) :
    OnCurve left → OnCurve right → OnCurve (add left right) :=
  LawfulAffine.onCurve_add curve left right two_ne_zero

/-- The pinned G1 membership predicate uses only ring operations, so it
transports exactly through `finEquiv`; unlike affine addition, no opaque
inverse is involved. -/
theorem onCurve_ofWire {x y : Fp}
    (hcurve : EvmSemantics.Crypto.Bls12381.onCurve x y = true) :
    OnCurve (ofWire (.affine x y)) := by
  simp only [EvmSemantics.Crypto.Bls12381.onCurve,
    EvmSemantics.Crypto.Weierstrass.onCurve] at hcurve
  change PrimeField.finEquiv y ^ 2 =
    PrimeField.finEquiv x ^ 3 + curve.a * PrimeField.finEquiv x + curve.b
  have hcurve' : y * y = x * (x * x) +
      EvmSemantics.Crypto.Bls12381.curve.a * x +
      EvmSemantics.Crypto.Bls12381.curve.b :=
    of_decide_eq_true hcurve
  have mapped := congrArg PrimeField.finEquiv hcurve'
  have hfour : PrimeField.finEquiv (4 : Fp) = (4 : Field) := by
    apply ZMod.val_injective
    rfl
  simpa [curve, EvmSemantics.Crypto.Bls12381.curve, hfour,
    pow_two, pow_succ, mul_assoc] using mapped

/-- Lawful membership transports back to the pinned decoded carrier because
the membership predicate itself does not use inversion. -/
theorem onCurve_toWire {x y : Field}
    (hcurve : OnCurve (.affine x y)) :
    EvmSemantics.Crypto.Bls12381.onCurve
      (PrimeField.finEquiv.symm x) (PrimeField.finEquiv.symm y) = true := by
  simp only [EvmSemantics.Crypto.Bls12381.onCurve,
    EvmSemantics.Crypto.Weierstrass.onCurve]
  apply decide_eq_true
  apply PrimeField.finEquiv.injective
  have hfour : PrimeField.finEquiv (4 : Fp) = (4 : Field) := by
    apply ZMod.val_injective
    rfl
  simpa [OnCurve, LawfulAffine.OnCurve, curve,
    EvmSemantics.Crypto.Bls12381.curve, hfour,
    pow_two, pow_succ, mul_assoc] using hcurve

end Challenge.Bls12381.ProofSupport.G1Affine
