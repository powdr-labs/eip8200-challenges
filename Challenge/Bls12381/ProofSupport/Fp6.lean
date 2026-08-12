import Challenge.Bls12381.ProofSupport.Fp2
import Challenge.Bls12381.ProofSupport.LawfulFp6

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.Fp6

open EvmSemantics.Crypto.Bls12381

structure Repr where
  c0 : Fp2.Repr
  c1 : Fp2.Repr
  c2 : Fp2.Repr
deriving DecidableEq

def toField (a : Repr) : EvmSemantics.Crypto.Bls12381.Fp6 :=
  { c0 := Fp2.toField a.c0, c1 := Fp2.toField a.c1, c2 := Fp2.toField a.c2 }

/-- Lawful algebraic interpretation of the executable cubic carrier. -/
def toLawful (a : Repr) : LawfulFp6.Carrier :=
  { c0 := Fp2.toLawful a.c0
    c1 := Fp2.toLawful a.c1
    c2 := Fp2.toLawful a.c2 }

def ofField (a : EvmSemantics.Crypto.Bls12381.Fp6) : Repr :=
  { c0 := Fp2.ofField a.c0, c1 := Fp2.ofField a.c1, c2 := Fp2.ofField a.c2 }

def Refines (a : Repr) (value : EvmSemantics.Crypto.Bls12381.Fp6) : Prop :=
  toField a = value

@[simp] theorem toField_ofField (a : EvmSemantics.Crypto.Bls12381.Fp6) :
    toField (ofField a) = a := by
  cases a
  simp [toField, ofField]

theorem refines_ofField (a : EvmSemantics.Crypto.Bls12381.Fp6) :
    Refines (ofField a) a := by
  simp [Refines]

def zero : Repr := { c0 := Fp2.zero, c1 := Fp2.zero, c2 := Fp2.zero }

def one : Repr := { c0 := Fp2.one, c1 := Fp2.zero, c2 := Fp2.zero }

/-- Multiplication by BLS12-381's sextic non-residue `1 + u`. -/
def mulByXi (a : Fp2.Repr) : Fp2.Repr :=
  { c0 := Fp.sub a.c0 a.c1, c1 := Fp.add a.c0 a.c1 }

@[simp] theorem semantic_mulByXi (a : EvmSemantics.Crypto.Bls12381.Fp2) :
    SexticNonResidue.mulByXi a =
      { c0 := a.c0 - a.c1, c1 := a.c0 + a.c1 } := rfl

def add (a b : Repr) : Repr :=
  { c0 := Fp2.add a.c0 b.c0
    c1 := Fp2.add a.c1 b.c1
    c2 := Fp2.add a.c2 b.c2 }

def sub (a b : Repr) : Repr :=
  { c0 := Fp2.sub a.c0 b.c0
    c1 := Fp2.sub a.c1 b.c1
    c2 := Fp2.sub a.c2 b.c2 }

def neg (a : Repr) : Repr :=
  { c0 := Fp2.neg a.c0, c1 := Fp2.neg a.c1, c2 := Fp2.neg a.c2 }

/-- Six-multiplication Karatsuba formula for the cubic extension. -/
def mul (a b : Repr) : Repr :=
  let v0 := Fp2.mul a.c0 b.c0
  let v1 := Fp2.mul a.c1 b.c1
  let v2 := Fp2.mul a.c2 b.c2
  let t0 := Fp2.mul (Fp2.add a.c1 a.c2) (Fp2.add b.c1 b.c2)
  let t1 := Fp2.mul (Fp2.add a.c0 a.c1) (Fp2.add b.c0 b.c1)
  let t2 := Fp2.mul (Fp2.add a.c0 a.c2) (Fp2.add b.c0 b.c2)
  { c0 := Fp2.add v0 (mulByXi (Fp2.sub (Fp2.sub t0 v1) v2))
    c1 := Fp2.add (Fp2.sub (Fp2.sub t1 v0) v1) (mulByXi v2)
    c2 := Fp2.sub (Fp2.sub (Fp2.add t2 v1) v0) v2 }

@[simp] theorem toLawful_mulByXi (a : Fp2.Repr) :
    Fp2.toLawful (mulByXi a) = LawfulFp6.xi * Fp2.toLawful a := by
  apply QuadraticAlgebra.ext <;>
    simp [mulByXi, LawfulFp6.xi, Fp2.toLawful, LawfulFp2.ofWire,
      Fp2.toField] <;> ring

@[simp] theorem toLawful_mul (a b : Repr) :
    toLawful (mul a b) = LawfulFp6.mul (toLawful a) (toLawful b) := by
  apply LawfulFp6.Carrier.ext
  · simp [mul, toLawful, LawfulFp6.mul]
    ring_nf
    simp
  · simp [mul, toLawful, LawfulFp6.mul]
    ring
  · simp [mul, toLawful, LawfulFp6.mul]
    ring

@[simp] theorem toLawful_add (a b : Repr) :
    toLawful (add a b) = LawfulFp6.add (toLawful a) (toLawful b) := by
  apply LawfulFp6.Carrier.ext <;>
    simp [toLawful, add, LawfulFp6.add]

@[simp] theorem toLawful_sub (a b : Repr) :
    toLawful (sub a b) = LawfulFp6.sub (toLawful a) (toLawful b) := by
  apply LawfulFp6.Carrier.ext <;>
    simp [toLawful, sub, LawfulFp6.sub]

@[simp] theorem toLawful_neg (a : Repr) :
    toLawful (neg a) = LawfulFp6.neg (toLawful a) := by
  apply LawfulFp6.Carrier.ext <;>
    simp [toLawful, neg, LawfulFp6.neg]

def square (a : Repr) : Repr :=
  let s0 := Fp2.square a.c0
  let s1 := Fp2.mul a.c0 a.c1
  let s2 := Fp2.mul a.c1 a.c2
  let s3 := Fp2.square a.c1
  let s4 := Fp2.mul a.c0 a.c2
  let s5 := Fp2.square a.c2
  { c0 := Fp2.add s0 (mulByXi (Fp2.add s2 s2))
    c1 := Fp2.add (Fp2.add s1 s1) (mulByXi s5)
    c2 := Fp2.add (Fp2.add s4 s4) s3 }

@[simp] theorem toLawful_square (a : Repr) :
    toLawful (square a) = LawfulFp6.mul (toLawful a) (toLawful a) := by
  apply LawfulFp6.Carrier.ext
  · simp [square, toLawful, LawfulFp6.mul]
    ring_nf
    simp
  · simp [square, toLawful, LawfulFp6.mul]
    ring
  · simp [square, toLawful, LawfulFp6.mul]
    ring

/-- Multiplication by the cubic generator `v`. -/
def mulByV (a : Repr) : Repr :=
  { c0 := mulByXi a.c2, c1 := a.c0, c2 := a.c1 }

@[simp] theorem toLawful_mulByV (a : Repr) :
    toLawful (mulByV a) = LawfulFp6.mulByV (toLawful a) := by
  apply LawfulFp6.Carrier.ext <;>
    simp [toLawful, mulByV, LawfulFp6.mulByV]

def mulByFp2 (a : Repr) (k : Fp2.Repr) : Repr :=
  { c0 := Fp2.mul a.c0 k, c1 := Fp2.mul a.c1 k, c2 := Fp2.mul a.c2 k }

/-- Component Frobenius map for the cubic extension, parameterized by the two
gamma constants selected by the requested Frobenius power. -/
def frobenius (gammaV gammaV2 : Fp2.Repr) (a : Repr) : Repr :=
  { c0 := Fp2.conj a.c0
    c1 := Fp2.mul gammaV (Fp2.conj a.c1)
    c2 := Fp2.mul gammaV2 (Fp2.conj a.c2) }

/-- Sparse multiplication by `(b0 + b1·v)`. -/
def mulBy01 (a : Repr) (b0 b1 : Fp2.Repr) : Repr :=
  let aa := Fp2.mul a.c0 b0
  let bb := Fp2.mul a.c1 b1
  let t1 := Fp2.add b0 b1
  { c0 := Fp2.add (mulByXi (Fp2.sub (Fp2.mul (Fp2.add a.c1 a.c2) b1) bb)) aa
    c1 := Fp2.sub (Fp2.sub (Fp2.mul t1 (Fp2.add a.c0 a.c1)) aa) bb
    c2 := Fp2.add (Fp2.sub (Fp2.mul (Fp2.add a.c0 a.c2) b0) aa) bb }

/-- Adjugate coefficients used by Fp6 inversion. -/
def invAdjugate (a : Repr) : Repr :=
  let t0 := Fp2.square a.c0
  let t1 := Fp2.square a.c1
  let t2 := Fp2.square a.c2
  let t3 := Fp2.mul a.c0 a.c1
  let t4 := Fp2.mul a.c0 a.c2
  let t5 := Fp2.mul a.c1 a.c2
  { c0 := Fp2.sub t0 (mulByXi t5)
    c1 := Fp2.sub (mulByXi t2) t3
    c2 := Fp2.sub t1 t4 }

def invNorm (a : Repr) : Fp2.Repr :=
  let adj := invAdjugate a
  Fp2.add (Fp2.mul a.c0 adj.c0)
    (mulByXi (Fp2.add (Fp2.mul a.c2 adj.c1) (Fp2.mul a.c1 adj.c2)))

/-- Actual Fp6 adjugate formula parameterized by an Fp2 inversion primitive. -/
def invWith (invert : Fp2.Repr → Fp2.Repr) (a : Repr) : Repr :=
  let adj := invAdjugate a
  let normInv := invert (invNorm a)
  { c0 := Fp2.mul adj.c0 normInv
    c1 := Fp2.mul adj.c1 normInv
    c2 := Fp2.mul adj.c2 normInv }

@[simp] theorem toLawful_invAdjugate (a : Repr) :
    toLawful (invAdjugate a) = LawfulFp6.adjugate (toLawful a) := by
  apply LawfulFp6.Carrier.ext
  · simp [toLawful, invAdjugate, LawfulFp6.adjugate]
    ring
  · simp [toLawful, invAdjugate, LawfulFp6.adjugate]
    ring_nf
    simp
  · simp [toLawful, invAdjugate, LawfulFp6.adjugate]
    ring

@[simp] theorem toLawful_invNorm (a : Repr) :
    Fp2.toLawful (invNorm a) = LawfulFp6.norm (toLawful a) := by
  simp only [invNorm, Fp2.toLawful_add, Fp2.toLawful_mul,
    toLawful_mulByXi]
  change (toLawful a).c0 * (toLawful (invAdjugate a)).c0 +
      LawfulFp6.xi * ((toLawful a).c2 * (toLawful (invAdjugate a)).c1 +
        (toLawful a).c1 * (toLawful (invAdjugate a)).c2) =
    LawfulFp6.norm (toLawful a)
  rw [toLawful_invAdjugate]
  rfl

/-- The executable Fp6 adjugate algorithm refines the lawful component
inverse under an Fp2 determinant-inversion refinement premise. -/
theorem toLawful_invWith (invert : Fp2.Repr → Fp2.Repr) (a : Repr)
    (hinvert : Fp2.toLawful (invert (invNorm a)) =
      (Fp2.toLawful (invNorm a))⁻¹) :
    toLawful (invWith invert a) = LawfulFp6.inv (toLawful a) := by
  have hscale : toLawful (invWith invert a) =
      LawfulFp6.scale (toLawful (invAdjugate a))
        (Fp2.toLawful (invert (invNorm a))) := by
    apply LawfulFp6.Carrier.ext <;>
      simp [toLawful, invWith, LawfulFp6.scale]
  rw [hscale, toLawful_invAdjugate, hinvert, toLawful_invNorm]
  rfl

def invSpecRepr (a : Repr) : Repr := ofField (_root_.Fp6.inv (toField a))

theorem mul_components (a b : Repr) :
    mul a b =
      let v0 := Fp2.mul a.c0 b.c0
      let v1 := Fp2.mul a.c1 b.c1
      let v2 := Fp2.mul a.c2 b.c2
      let t0 := Fp2.mul (Fp2.add a.c1 a.c2) (Fp2.add b.c1 b.c2)
      let t1 := Fp2.mul (Fp2.add a.c0 a.c1) (Fp2.add b.c0 b.c1)
      let t2 := Fp2.mul (Fp2.add a.c0 a.c2) (Fp2.add b.c0 b.c2)
      { c0 := Fp2.add v0 (mulByXi (Fp2.sub (Fp2.sub t0 v1) v2))
        c1 := Fp2.add (Fp2.sub (Fp2.sub t1 v0) v1) (mulByXi v2)
        c2 := Fp2.sub (Fp2.sub (Fp2.add t2 v1) v0) v2 } := rfl

@[simp] theorem toField_mulByXi (a : Fp2.Repr) :
    Fp2.toField (mulByXi a) =
      instBls12381SexticNonResidue.mulByXi
        (Fp2.toField a) := by
  change
    ({ c0 := Fp.toField (Fp.sub a.c0 a.c1)
       c1 := Fp.toField (Fp.add a.c0 a.c1) } :
      EvmSemantics.Crypto.Bls12381.Fp2) = _
  simp [Fp2.toField]

theorem refines_add (a b : Repr) : Refines (add a b) (toField a + toField b) := by
  change toField (add a b) = _root_.Fp6.add (toField a) (toField b)
  simp [add, toField, _root_.Fp6.add]
theorem refines_sub (a b : Repr) : Refines (sub a b) (toField a - toField b) := by
  change toField (sub a b) = _root_.Fp6.sub (toField a) (toField b)
  simp [sub, toField, _root_.Fp6.sub]
theorem refines_neg (a : Repr) : Refines (neg a) (-toField a) := by
  change toField (neg a) = _root_.Fp6.neg (toField a)
  simp [neg, toField, _root_.Fp6.neg]
theorem refines_mul (a b : Repr) : Refines (mul a b) (toField a * toField b) := by
  change toField (mul a b) = _root_.Fp6.mul (toField a) (toField b)
  simp [mul, toField, _root_.Fp6.mul]
theorem refines_square (a : Repr) :
    Refines (square a) (_root_.Fp6.square (toField a)) := by
  change toField (square a) = _root_.Fp6.square (toField a)
  simp [square, toField, _root_.Fp6.square]
theorem refines_mulBy01 (a : Repr) (b0 b1 : Fp2.Repr) :
    Refines (mulBy01 a b0 b1)
      (_root_.Fp6.mulBy01 (toField a) (Fp2.toField b0) (Fp2.toField b1)) := by
  change toField (mulBy01 a b0 b1) =
    _root_.Fp6.mulBy01 (toField a) (Fp2.toField b0) (Fp2.toField b1)
  simp [mulBy01, toField, _root_.Fp6.mulBy01]

@[simp] theorem toField_invAdjugate (a : Repr) :
    toField (invAdjugate a) =
      let t0 := (Fp2.toField a.c0) ^ 2
      let t1 := (Fp2.toField a.c1) ^ 2
      let t2 := (Fp2.toField a.c2) ^ 2
      let t3 := Fp2.toField a.c0 * Fp2.toField a.c1
      let t4 := Fp2.toField a.c0 * Fp2.toField a.c2
      let t5 := Fp2.toField a.c1 * Fp2.toField a.c2
      { c0 := t0 - SexticNonResidue.mulByXi t5
        c1 := SexticNonResidue.mulByXi t2 - t3
        c2 := t1 - t4 } := by
  simp [invAdjugate, toField]

@[simp] theorem toField_invNorm (a : Repr) :
    Fp2.toField (invNorm a) =
      let adj := toField (invAdjugate a)
      Fp2.toField a.c0 * adj.c0 +
        SexticNonResidue.mulByXi
          (Fp2.toField a.c2 * adj.c1 + Fp2.toField a.c1 * adj.c2) := by
  simp [invNorm, toField]

theorem refines_invWith (invert : Fp2.Repr → Fp2.Repr) (a : Repr)
    (hinvert : Fp2.toField (invert (invNorm a)) =
      _root_.Fp2.inv (Fp2.toField (invNorm a))) :
    Refines (invWith invert a) (_root_.Fp6.inv (toField a)) := by
  let adj := invAdjugate a
  let n := invNorm a
  have hsemantic : _root_.Fp6.inv (toField a) =
      { c0 := (toField adj).c0 * _root_.Fp2.inv (Fp2.toField n)
        c1 := (toField adj).c1 * _root_.Fp2.inv (Fp2.toField n)
        c2 := (toField adj).c2 * _root_.Fp2.inv (Fp2.toField n) } := by
    simp [adj, n, invAdjugate, invNorm, toField, _root_.Fp6.inv]
  change toField (invWith invert a) = _root_.Fp6.inv (toField a)
  rw [hsemantic]
  change
    ({ c0 := Fp2.toField (Fp2.mul adj.c0 (invert n))
       c1 := Fp2.toField (Fp2.mul adj.c1 (invert n))
       c2 := Fp2.toField (Fp2.mul adj.c2 (invert n)) } :
      EvmSemantics.Crypto.Bls12381.Fp6) = _
  have hinvert' : Fp2.toField (invert n) =
      _root_.Fp2.inv (Fp2.toField n) := by simpa [n] using hinvert
  simp [hinvert', toField]

theorem refines_invSpecRepr (a : Repr) :
    Refines (invSpecRepr a) (_root_.Fp6.inv (toField a)) := refines_ofField _

@[simp] theorem toField_add (a b : Repr) :
    toField (add a b) = toField a + toField b := refines_add a b
@[simp] theorem toField_sub (a b : Repr) :
    toField (sub a b) = toField a - toField b := refines_sub a b
@[simp] theorem toField_neg (a : Repr) :
    toField (neg a) = -toField a := refines_neg a
@[simp] theorem toField_mul (a b : Repr) :
    toField (mul a b) = toField a * toField b := refines_mul a b
@[simp] theorem toField_square (a : Repr) :
    toField (square a) = _root_.Fp6.square (toField a) := refines_square a
@[simp] theorem toField_mulByV (a : Repr) :
    toField (mulByV a) = _root_.Fp6.mulByV (toField a) := by
  change
    ({ c0 := Fp2.toField (mulByXi a.c2)
       c1 := Fp2.toField a.c0
       c2 := Fp2.toField a.c1 } : EvmSemantics.Crypto.Bls12381.Fp6) = _
  simp [_root_.Fp6.mulByV, toField]
@[simp] theorem toField_mulByFp2 (a : Repr) (k : Fp2.Repr) :
    toField (mulByFp2 a k) = _root_.Fp6.mulByFp2 (toField a) (Fp2.toField k) := by
  simp [mulByFp2, toField, _root_.Fp6.mulByFp2]
@[simp] theorem toField_frobenius (gammaV gammaV2 : Fp2.Repr) (a : Repr) :
    toField (frobenius gammaV gammaV2 a) =
      { c0 := _root_.Fp2.conj (Fp2.toField a.c0)
        c1 := Fp2.toField gammaV * _root_.Fp2.conj (Fp2.toField a.c1)
        c2 := Fp2.toField gammaV2 * _root_.Fp2.conj (Fp2.toField a.c2) } := by
  simp [frobenius, toField]
@[simp] theorem toField_mulBy01 (a : Repr) (b0 b1 : Fp2.Repr) :
    toField (mulBy01 a b0 b1) =
      _root_.Fp6.mulBy01 (toField a) (Fp2.toField b0) (Fp2.toField b1) :=
  refines_mulBy01 a b0 b1
@[simp] theorem toField_invWith (invert : Fp2.Repr → Fp2.Repr) (a : Repr)
    (hinvert : Fp2.toField (invert (invNorm a)) =
      _root_.Fp2.inv (Fp2.toField (invNorm a))) :
    toField (invWith invert a) = _root_.Fp6.inv (toField a) :=
  refines_invWith invert a hinvert
@[simp] theorem toField_invSpecRepr (a : Repr) :
    toField (invSpecRepr a) = _root_.Fp6.inv (toField a) := refines_invSpecRepr a

@[simp] theorem toField_zero : toField zero = 0 := by
  change ({ c0 := 0, c1 := 0, c2 := 0 } :
    EvmSemantics.Crypto.Bls12381.Fp6) = _root_.Fp6.zero
  rfl

@[simp] theorem toField_one : toField one = 1 := by
  change ({ c0 := 1, c1 := 0, c2 := 0 } :
    EvmSemantics.Crypto.Bls12381.Fp6) = _root_.Fp6.one
  rfl

@[simp] theorem semantic_pow_two (a : EvmSemantics.Crypto.Bls12381.Fp6) :
    a ^ 2 = _root_.Fp6.square a := rfl

end Challenge.Bls12381.ProofSupport.Fp6
