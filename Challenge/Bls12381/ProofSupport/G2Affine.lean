import Challenge.Bls12381.ProofSupport.LawfulAffine
import Challenge.Bls12381.ProofSupport.LawfulFp2

set_option warningAsError true

/-! # Lawful affine BLS12-381 G2 boundary -/

namespace Challenge.Bls12381.ProofSupport.G2Affine

open EvmSemantics.Crypto.Bls12381

abbrev Field := LawfulFp2.Carrier
abbrev Point := LawfulAffine.Point Field

/-- The lawful BLS12-381 G2 twist `y² = x³ + 4*(1+u)`. -/
def curve : LawfulAffine.Curve Field :=
  { a := 0, b := LawfulFp2.ofWire g2TwistB }

abbrev infinity : Point := .infinity
abbrev OnCurve : Point → Prop := LawfulAffine.OnCurve curve

def neg : Point → Point := LawfulAffine.neg
def double : Point → Point := LawfulAffine.double curve
def add : Point → Point → Point := LawfulAffine.add curve

/-- Inverse-free conversion from the decoded EIP wire carrier. -/
def ofWire : EvmSemantics.Crypto.Bls12381.G2Point → Point
  | .infinity => .infinity
  | .affine x y => .affine (LawfulFp2.ofWire x) (LawfulFp2.ofWire y)

/-- Inverse-free conversion back to the decoded EIP wire carrier. -/
def toWire : Point → EvmSemantics.Crypto.Bls12381.G2Point
  | .infinity => .infinity
  | .affine x y => .affine (LawfulFp2.toWire x) (LawfulFp2.toWire y)

@[simp] theorem toWire_ofWire (point : EvmSemantics.Crypto.Bls12381.G2Point) :
    toWire (ofWire point) = point := by
  cases point <;> simp [toWire, ofWire]

@[simp] theorem ofWire_toWire (point : Point) :
    ofWire (toWire point) = point := by
  cases point <;> simp [toWire, ofWire]

theorem two_ne_zero : (2 : Field) ≠ 0 := by
  intro hzero
  have hbase : (2 : LawfulFp2.Base) ≠ 0 := by
    change ((2 : Nat) : ZMod p) ≠ 0
    intro hbaseZero
    have hdiv : p ∣ 2 :=
      (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hbaseZero
    norm_num [p, absU] at hdiv
  apply hbase
  have hre := congrArg QuadraticAlgebra.re hzero
  simpa only [QuadraticAlgebra.re_ofNat, QuadraticAlgebra.re_zero] using hre

theorem onCurve_double (point : Point) :
    OnCurve point → OnCurve (double point) :=
  LawfulAffine.onCurve_double curve point two_ne_zero

theorem onCurve_add (left right : Point) :
    OnCurve left → OnCurve right → OnCurve (add left right) :=
  LawfulAffine.onCurve_add curve left right two_ne_zero

/-- The pinned G2 membership predicate is inverse-free and therefore
transports exactly through the lawful `Fp2` adapter. -/
theorem onCurve_ofWire {x y : EvmSemantics.Crypto.Bls12381.Fp2}
    (hcurve : EvmSemantics.Crypto.G2.onCurve
      EvmSemantics.Crypto.Bls12381.g2Curve x y = true) :
    OnCurve (ofWire (.affine x y)) := by
  simp only [EvmSemantics.Crypto.G2.onCurve] at hcurve
  have hcurve' : y ^ 2 = x * x ^ 2 + g2TwistB := by
    have hparts :
        (y ^ 2).c0 = (x * x ^ 2 + g2TwistB).c0 ∧
        (y ^ 2).c1 = (x * x ^ 2 + g2TwistB).c1 := by
      simpa [EvmSemantics.Crypto.Bls12381.g2Curve, _root_.Fp2.eq] using hcurve
    cases hleft : y ^ 2 with
    | mk yc0 yc1 =>
        cases hright : x * x ^ 2 + g2TwistB with
        | mk rc0 rc1 =>
            rw [hleft, hright] at hparts
            rw [_root_.Fp2.mk.injEq]
            simpa using hparts
  change LawfulFp2.ofWire y ^ 2 =
    LawfulFp2.ofWire x ^ 3 + curve.a * LawfulFp2.ofWire x + curve.b
  rw [show LawfulFp2.ofWire y ^ 2 = LawfulFp2.ofWire (y ^ 2) by
      symm; exact LawfulFp2.ofWire_square y]
  rw [hcurve']
  simp [curve, pow_succ, mul_assoc]

/-- Lawful G2 membership transports back to the inverse-free pinned
membership predicate. -/
theorem onCurve_toWire {x y : Field}
    (hcurve : OnCurve (.affine x y)) :
    EvmSemantics.Crypto.G2.onCurve EvmSemantics.Crypto.Bls12381.g2Curve
      (LawfulFp2.toWire x) (LawfulFp2.toWire y) = true := by
  have hlawful :
      LawfulFp2.ofWire ((LawfulFp2.toWire y) ^ 2) =
        LawfulFp2.ofWire
          (LawfulFp2.toWire x * (LawfulFp2.toWire x) ^ 2 + g2TwistB) := by
    simpa [OnCurve, LawfulAffine.OnCurve, curve, pow_succ, mul_assoc] using hcurve
  have hwire' :
      (LawfulFp2.toWire y) ^ 2 =
        LawfulFp2.toWire x * (LawfulFp2.toWire x) ^ 2 + g2TwistB := by
    apply LawfulFp2.ofWire_injective
    simpa using hlawful
  have hparts :
      ((LawfulFp2.toWire y) ^ 2).c0 =
          (LawfulFp2.toWire x * (LawfulFp2.toWire x) ^ 2 + g2TwistB).c0 ∧
        ((LawfulFp2.toWire y) ^ 2).c1 =
          (LawfulFp2.toWire x * (LawfulFp2.toWire x) ^ 2 + g2TwistB).c1 :=
    ⟨congrArg _root_.Fp2.c0 hwire', congrArg _root_.Fp2.c1 hwire'⟩
  simp only [EvmSemantics.Crypto.G2.onCurve,
    EvmSemantics.Crypto.Bls12381.g2Curve, _root_.Fp2.eq]
  simpa using hparts

end Challenge.Bls12381.ProofSupport.G2Affine
