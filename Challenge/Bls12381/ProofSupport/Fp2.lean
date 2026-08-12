import Challenge.Bls12381.ProofSupport.Fp
import Challenge.Bls12381.ProofSupport.LawfulFp2

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.Fp2

open EvmSemantics.Crypto.Bls12381

structure Repr where
  c0 : Fp.Limbs
  c1 : Fp.Limbs
deriving DecidableEq

def toField (a : Repr) : EvmSemantics.Crypto.Bls12381.Fp2 :=
  { c0 := Fp.toField a.c0, c1 := Fp.toField a.c1 }

/-- Lawful algebraic interpretation of the executable two-limb carrier. -/
def toLawful (a : Repr) : LawfulFp2.Carrier :=
  LawfulFp2.ofWire (toField a)

def ofField (a : EvmSemantics.Crypto.Bls12381.Fp2) : Repr :=
  { c0 := Fp.ofField a.c0, c1 := Fp.ofField a.c1 }

def Refines (a : Repr) (value : EvmSemantics.Crypto.Bls12381.Fp2) : Prop :=
  toField a = value

@[simp] theorem toField_ofField (a : EvmSemantics.Crypto.Bls12381.Fp2) :
    toField (ofField a) = a := by
  cases a
  simp [toField, ofField]

theorem refines_ofField (a : EvmSemantics.Crypto.Bls12381.Fp2) :
    Refines (ofField a) a := by
  simp [Refines]

def zero : Repr := { c0 := Fp.normalize 0, c1 := Fp.normalize 0 }

def one : Repr := { c0 := Fp.normalize 1, c1 := Fp.normalize 0 }

/-- Componentwise addition over the two-word base-field representation. -/
def add (a b : Repr) : Repr :=
  { c0 := Fp.add a.c0 b.c0, c1 := Fp.add a.c1 b.c1 }

/-- Componentwise subtraction over the two-word base-field representation. -/
def sub (a b : Repr) : Repr :=
  { c0 := Fp.sub a.c0 b.c0, c1 := Fp.sub a.c1 b.c1 }

/-- Karatsuba multiplication using three base-field multiplications. -/
def mul (a b : Repr) : Repr :=
  let t0 := Fp.mul a.c0 b.c0
  let t1 := Fp.mul a.c1 b.c1
  let c0 := Fp.sub t0 t1
  let s := Fp.mul (Fp.add a.c0 a.c1) (Fp.add b.c0 b.c1)
  let c1 := Fp.sub (Fp.sub s t0) t1
  { c0, c1 }

/-- Specialised Fp2 squaring using two base-field multiplications. -/
def square (a : Repr) : Repr :=
  { c0 := Fp.mul (Fp.add a.c0 a.c1) (Fp.sub a.c0 a.c1)
    c1 := Fp.mul (Fp.add a.c0 a.c0) a.c1 }

def neg (a : Repr) : Repr := { c0 := Fp.neg a.c0, c1 := Fp.neg a.c1 }

/-- Component-level conjugation; unlike `ofField`, this is directly
implementable using one base-field negation. -/
def conj (a : Repr) : Repr := { c0 := a.c0, c1 := Fp.neg a.c1 }

/-- Norm `a₀² + a₁²`, represented over the two-word base field. -/
def norm (a : Repr) : Fp.Limbs :=
  Fp.add (Fp.mul a.c0 a.c0) (Fp.mul a.c1 a.c1)

/-- Actual Fp2 adjugate formula, parameterized by the base-field inversion
algorithm.  This makes the only still-unproved primitive explicit rather than
hiding it behind an affine semantic operation. -/
def invWith (invert : Fp.Limbs → Fp.Limbs) (a : Repr) : Repr :=
  let normInv := invert (norm a)
  { c0 := Fp.mul a.c0 normInv
    c1 := Fp.mul (Fp.neg a.c1) normInv }

/-- Mathematical inverse representation retained as an explicitly named spec
adapter; concrete code must refine `invWith` instead. -/
def invSpecRepr (a : Repr) : Repr := ofField (toField a)⁻¹

theorem mul_components (a b : Repr) :
    mul a b =
      let t0 := Fp.mul a.c0 b.c0
      let t1 := Fp.mul a.c1 b.c1
      { c0 := Fp.sub t0 t1
        c1 := Fp.sub
          (Fp.sub (Fp.mul (Fp.add a.c0 a.c1) (Fp.add b.c0 b.c1)) t0) t1 } := rfl

theorem refines_add (a b : Repr) : Refines (add a b) (toField a + toField b) := by
  change
    ({ c0 := Fp.toField (Fp.add a.c0 b.c0)
       c1 := Fp.toField (Fp.add a.c1 b.c1) } :
      EvmSemantics.Crypto.Bls12381.Fp2) =
    ({ c0 := Fp.toField a.c0 + Fp.toField b.c0
       c1 := Fp.toField a.c1 + Fp.toField b.c1 } :
      EvmSemantics.Crypto.Bls12381.Fp2)
  rw [Fp.toField_add, Fp.toField_add]
theorem refines_sub (a b : Repr) : Refines (sub a b) (toField a - toField b) := by
  change
    ({ c0 := Fp.toField (Fp.sub a.c0 b.c0)
       c1 := Fp.toField (Fp.sub a.c1 b.c1) } :
      EvmSemantics.Crypto.Bls12381.Fp2) =
    ({ c0 := Fp.toField a.c0 - Fp.toField b.c0
       c1 := Fp.toField a.c1 - Fp.toField b.c1 } :
      EvmSemantics.Crypto.Bls12381.Fp2)
  rw [Fp.toField_sub, Fp.toField_sub]
theorem refines_mul (a b : Repr) : Refines (mul a b) (toField a * toField b) := by
  change
    ({ c0 := Fp.toField (Fp.sub (Fp.mul a.c0 b.c0) (Fp.mul a.c1 b.c1))
       c1 := Fp.toField (Fp.sub
        (Fp.sub (Fp.mul (Fp.add a.c0 a.c1) (Fp.add b.c0 b.c1))
          (Fp.mul a.c0 b.c0)) (Fp.mul a.c1 b.c1)) } :
      EvmSemantics.Crypto.Bls12381.Fp2) =
    _root_.Fp2.mul (toField a) (toField b)
  simp [toField, _root_.Fp2.mul]
theorem refines_square (a : Repr) :
    Refines (square a) (_root_.Fp2.square (toField a)) := by
  change
    ({ c0 := Fp.toField (Fp.mul (Fp.add a.c0 a.c1) (Fp.sub a.c0 a.c1))
       c1 := Fp.toField (Fp.mul (Fp.add a.c0 a.c0) a.c1) } :
      EvmSemantics.Crypto.Bls12381.Fp2) =
    _root_.Fp2.square (toField a)
  simp [toField, _root_.Fp2.square]
theorem refines_neg (a : Repr) : Refines (neg a) (-toField a) := by
  change
    ({ c0 := Fp.toField (Fp.neg a.c0), c1 := Fp.toField (Fp.neg a.c1) } :
      EvmSemantics.Crypto.Bls12381.Fp2) =
    _root_.Fp2.neg (toField a)
  simp [toField, _root_.Fp2.neg]
theorem refines_conj (a : Repr) :
    Refines (conj a) (_root_.Fp2.conj (toField a)) := by
  change
    ({ c0 := Fp.toField a.c0, c1 := Fp.toField (Fp.neg a.c1) } :
      EvmSemantics.Crypto.Bls12381.Fp2) = _root_.Fp2.conj (toField a)
  simp [toField, _root_.Fp2.conj]

@[simp] theorem toField_norm (a : Repr) :
    Fp.toField (norm a) = _root_.Fp2.norm (toField a) := by
  simp [norm, toField, _root_.Fp2.norm]

theorem refines_invWith (invert : Fp.Limbs → Fp.Limbs) (a : Repr)
    (hinvert : Fp.toField (invert (norm a)) =
      (Fp.toField (norm a))⁻¹) :
    Refines (invWith invert a) (_root_.Fp2.inv (toField a)) := by
  change
    ({ c0 := Fp.toField (Fp.mul a.c0 (invert (norm a)))
       c1 := Fp.toField (Fp.mul (Fp.neg a.c1) (invert (norm a))) } :
      EvmSemantics.Crypto.Bls12381.Fp2) = _root_.Fp2.inv (toField a)
  simp [hinvert, toField_norm, toField, _root_.Fp2.inv,
    _root_.Fp2.norm]

/-- The component inversion algorithm refines the lawful quadratic-field
inverse.  Its only premise is the base-field inversion algorithm's lawful
refinement, never equality to the pinned opaque `FF.modInv`. -/
theorem toLawful_invWith (invert : Fp.Limbs → Fp.Limbs) (a : Repr)
    (hinvert : PrimeField.finEquiv (Fp.toField (invert (norm a))) =
      (PrimeField.finEquiv (Fp.toField (norm a)))⁻¹) :
    toLawful (invWith invert a) = (toLawful a)⁻¹ := by
  simp [norm] at hinvert
  apply QuadraticAlgebra.ext
  · simp [toLawful, LawfulFp2.ofWire, toField, invWith, norm,
      QuadraticAlgebra.inv_def, QuadraticAlgebra.norm_def, hinvert, mul_comm]
  · simp [toLawful, LawfulFp2.ofWire, toField, invWith, norm,
      QuadraticAlgebra.inv_def, QuadraticAlgebra.norm_def, hinvert, mul_comm]

@[simp] theorem toLawful_add (a b : Repr) :
    toLawful (add a b) = toLawful a + toLawful b := by
  apply QuadraticAlgebra.ext <;>
    simp [toLawful, LawfulFp2.ofWire, toField, add]

@[simp] theorem toLawful_sub (a b : Repr) :
    toLawful (sub a b) = toLawful a - toLawful b := by
  apply QuadraticAlgebra.ext <;>
    simp [toLawful, LawfulFp2.ofWire, toField, sub]

@[simp] theorem toLawful_mul (a b : Repr) :
    toLawful (mul a b) = toLawful a * toLawful b := by
  apply QuadraticAlgebra.ext <;>
    simp [toLawful, LawfulFp2.ofWire, toField, mul] <;> ring

@[simp] theorem toLawful_square (a : Repr) :
    toLawful (square a) = toLawful a * toLawful a := by
  apply QuadraticAlgebra.ext <;>
    simp [toLawful, LawfulFp2.ofWire, toField, square] <;> ring

@[simp] theorem toLawful_neg (a : Repr) :
    toLawful (neg a) = -toLawful a := by
  apply QuadraticAlgebra.ext <;>
    simp [toLawful, LawfulFp2.ofWire, toField, neg]

theorem refines_invSpecRepr (a : Repr) :
    Refines (invSpecRepr a) (toField a)⁻¹ := refines_ofField _

@[simp] theorem toField_add (a b : Repr) :
    toField (add a b) = toField a + toField b := refines_add a b
@[simp] theorem toField_sub (a b : Repr) :
    toField (sub a b) = toField a - toField b := refines_sub a b
@[simp] theorem toField_mul (a b : Repr) :
    toField (mul a b) = toField a * toField b := refines_mul a b
@[simp] theorem toField_square (a : Repr) :
    toField (square a) = _root_.Fp2.square (toField a) := refines_square a
@[simp] theorem toField_neg (a : Repr) :
    toField (neg a) = -toField a := refines_neg a
@[simp] theorem toField_conj (a : Repr) :
    toField (conj a) = _root_.Fp2.conj (toField a) := refines_conj a
@[simp] theorem toField_invWith (invert : Fp.Limbs → Fp.Limbs) (a : Repr)
    (hinvert : Fp.toField (invert (norm a)) =
      (Fp.toField (norm a))⁻¹) :
    toField (invWith invert a) = _root_.Fp2.inv (toField a) :=
  refines_invWith invert a hinvert
@[simp] theorem toField_invSpecRepr (a : Repr) :
    toField (invSpecRepr a) = (toField a)⁻¹ := refines_invSpecRepr a

@[simp] theorem toField_zero : toField zero = 0 := by
  change ({ c0 := 0, c1 := 0 } : EvmSemantics.Crypto.Bls12381.Fp2) =
    _root_.Fp2.zero
  rfl

@[simp] theorem toField_one : toField one = 1 := by
  change ({ c0 := 1, c1 := 0 } : EvmSemantics.Crypto.Bls12381.Fp2) =
    _root_.Fp2.one
  rfl

@[simp] theorem semantic_pow_two (a : EvmSemantics.Crypto.Bls12381.Fp2) :
    a ^ 2 = _root_.Fp2.square a := rfl

end Challenge.Bls12381.ProofSupport.Fp2
