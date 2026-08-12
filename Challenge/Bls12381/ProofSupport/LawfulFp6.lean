import Challenge.Bls12381.ProofSupport.LawfulFp2

set_option warningAsError true

/-! Lawful component carrier for the BLS12-381 cubic extension. -/

namespace Challenge.Bls12381.ProofSupport.LawfulFp6

@[ext] structure Carrier where
  c0 : LawfulFp2.Carrier
  c1 : LawfulFp2.Carrier
  c2 : LawfulFp2.Carrier
deriving DecidableEq

def zero : Carrier := { c0 := 0, c1 := 0, c2 := 0 }

def add (a b : Carrier) : Carrier :=
  { c0 := a.c0 + b.c0, c1 := a.c1 + b.c1, c2 := a.c2 + b.c2 }

def sub (a b : Carrier) : Carrier :=
  { c0 := a.c0 - b.c0, c1 := a.c1 - b.c1, c2 := a.c2 - b.c2 }

def neg (a : Carrier) : Carrier :=
  { c0 := -a.c0, c1 := -a.c1, c2 := -a.c2 }

/-- The sextic non-residue `1 + u` in the lawful quadratic field. -/
def xi : LawfulFp2.Carrier := ⟨1, 1⟩

/-- Cubic-extension multiplication reduced by `v³ = 1 + u`. -/
def mul (a b : Carrier) : Carrier :=
  { c0 := a.c0 * b.c0 + xi * (a.c1 * b.c2 + a.c2 * b.c1)
    c1 := a.c0 * b.c1 + a.c1 * b.c0 + xi * (a.c2 * b.c2)
    c2 := a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 }

def mulByV (a : Carrier) : Carrier :=
  { c0 := xi * a.c2, c1 := a.c0, c2 := a.c1 }

def one : Carrier := { c0 := 1, c1 := 0, c2 := 0 }

/-- Cubic adjugate used by inversion. -/
def adjugate (a : Carrier) : Carrier :=
  { c0 := a.c0 ^ 2 - xi * (a.c1 * a.c2)
    c1 := xi * (a.c2 ^ 2) - a.c0 * a.c1
    c2 := a.c1 ^ 2 - a.c0 * a.c2 }

/-- Determinant of multiplication by a cubic-extension element. -/
def norm (a : Carrier) : LawfulFp2.Carrier :=
  let adj := adjugate a
  a.c0 * adj.c0 + xi * (a.c2 * adj.c1 + a.c1 * adj.c2)

def scale (a : Carrier) (k : LawfulFp2.Carrier) : Carrier :=
  { c0 := a.c0 * k, c1 := a.c1 * k, c2 := a.c2 * k }

/-- Lawful component inversion formula.  This is executable field arithmetic,
not a call to the pinned semantic inverse. -/
def inv (a : Carrier) : Carrier := scale (adjugate a) (norm a)⁻¹

/-- The component formula is a multiplicative inverse whenever its Fp2
determinant is nonzero. -/
theorem mul_inv_of_norm_ne_zero (a : Carrier) (hnorm : norm a ≠ 0) :
    mul a (inv a) = one := by
  have hcancel : norm a * (norm a)⁻¹ = 1 := by
    simpa [mul_comm] using inv_mul_cancel₀ hnorm
  apply Carrier.ext
  · change
      a.c0 * ((adjugate a).c0 * (norm a)⁻¹) +
          xi * (a.c1 * ((adjugate a).c2 * (norm a)⁻¹) +
            a.c2 * ((adjugate a).c1 * (norm a)⁻¹)) = 1
    calc
      _ = norm a * (norm a)⁻¹ := by
        simp [norm]
        ring
      _ = 1 := hcancel
  · change
      a.c0 * ((adjugate a).c1 * (norm a)⁻¹) +
          a.c1 * ((adjugate a).c0 * (norm a)⁻¹) +
          xi * (a.c2 * ((adjugate a).c2 * (norm a)⁻¹)) = 0
    simp [adjugate]
    ring
  · change
      a.c0 * ((adjugate a).c2 * (norm a)⁻¹) +
          a.c1 * ((adjugate a).c1 * (norm a)⁻¹) +
          a.c2 * ((adjugate a).c0 * (norm a)⁻¹) = 0
    simp [adjugate]
    ring

theorem mul_comm (a b : Carrier) : mul a b = mul b a := by
  apply Carrier.ext <;> simp [mul] <;> ring

theorem inv_mul_of_norm_ne_zero (a : Carrier) (hnorm : norm a ≠ 0) :
    mul (inv a) a = one := by
  rw [mul_comm]
  exact mul_inv_of_norm_ne_zero a hnorm

/-- Inverse-free adapter from the pinned three-component wire carrier. -/
def ofWire (a : EvmSemantics.Crypto.Bls12381.Fp6) : Carrier :=
  { c0 := LawfulFp2.ofWire a.c0
    c1 := LawfulFp2.ofWire a.c1
    c2 := LawfulFp2.ofWire a.c2 }

/-- Inverse-free adapter back to the pinned wire carrier. -/
def toWire (a : Carrier) : EvmSemantics.Crypto.Bls12381.Fp6 :=
  { c0 := LawfulFp2.toWire a.c0
    c1 := LawfulFp2.toWire a.c1
    c2 := LawfulFp2.toWire a.c2 }

@[simp] theorem toWire_ofWire (a : EvmSemantics.Crypto.Bls12381.Fp6) :
    toWire (ofWire a) = a := by
  cases a
  simp [toWire, ofWire]

@[simp] theorem ofWire_toWire (a : Carrier) : ofWire (toWire a) = a := by
  cases a
  simp [toWire, ofWire]

end Challenge.Bls12381.ProofSupport.LawfulFp6
