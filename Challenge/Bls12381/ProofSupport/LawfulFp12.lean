import Challenge.Bls12381.ProofSupport.LawfulFp6

set_option warningAsError true

/-! Lawful component carrier for the BLS12-381 quadratic-over-cubic tower. -/

namespace Challenge.Bls12381.ProofSupport.LawfulFp12

@[ext] structure Carrier where
  c0 : LawfulFp6.Carrier
  c1 : LawfulFp6.Carrier
deriving DecidableEq

/-- Quadratic-over-cubic Karatsuba multiplication with `w² = v`. -/
def mul (a b : Carrier) : Carrier :=
  let v0 := LawfulFp6.mul a.c0 b.c0
  let v1 := LawfulFp6.mul a.c1 b.c1
  let t := LawfulFp6.mul (LawfulFp6.add a.c0 a.c1)
    (LawfulFp6.add b.c0 b.c1)
  { c0 := LawfulFp6.add v0 (LawfulFp6.mulByV v1)
    c1 := LawfulFp6.sub (LawfulFp6.sub t v0) v1 }

def zero : Carrier := { c0 := LawfulFp6.zero, c1 := LawfulFp6.zero }

def one : Carrier := { c0 := LawfulFp6.one, c1 := LawfulFp6.zero }

/-- Quadratic norm `c0² - v·c1²` used by the lawful component inverse. -/
def norm (a : Carrier) : LawfulFp6.Carrier :=
  LawfulFp6.sub (LawfulFp6.mul a.c0 a.c0)
    (LawfulFp6.mulByV (LawfulFp6.mul a.c1 a.c1))

/-- Lawful quadratic-extension inverse formula, expressed only through the
component arithmetic of the local field tower. -/
def inv (a : Carrier) : Carrier :=
  let normInv := LawfulFp6.inv (norm a)
  { c0 := LawfulFp6.mul a.c0 normInv
    c1 := LawfulFp6.neg (LawfulFp6.mul a.c1 normInv) }

/-- The lawful component formula is a right inverse whenever the Fp2
determinant underlying its Fp6 norm is nonzero. -/
theorem mul_inv_of_norm_ne_zero (a : Carrier)
    (hnorm : LawfulFp6.norm (norm a) ≠ 0) :
    mul a (inv a) = one := by
  unfold inv mul
  dsimp only
  apply Carrier.ext
  · calc
      _ = LawfulFp6.mul (norm a) (LawfulFp6.inv (norm a)) := by
        apply LawfulFp6.Carrier.ext <;>
          simp [norm, LawfulFp6.mul, LawfulFp6.add, LawfulFp6.sub,
            LawfulFp6.neg, LawfulFp6.mulByV] <;> ring
      _ = LawfulFp6.one := LawfulFp6.mul_inv_of_norm_ne_zero (norm a) hnorm
  · apply LawfulFp6.Carrier.ext <;>
      simp [one, LawfulFp6.zero, LawfulFp6.mul, LawfulFp6.add,
        LawfulFp6.sub, LawfulFp6.neg] <;> ring

theorem mul_comm (a b : Carrier) : mul a b = mul b a := by
  apply Carrier.ext <;>
    apply LawfulFp6.Carrier.ext <;>
      simp [mul, LawfulFp6.mul, LawfulFp6.add, LawfulFp6.sub,
        LawfulFp6.mulByV] <;> ring

/-- The lawful component formula is also a left inverse under the same
determinant nonzero boundary. -/
theorem inv_mul_of_norm_ne_zero (a : Carrier)
    (hnorm : LawfulFp6.norm (norm a) ≠ 0) :
    mul (inv a) a = one := by
  rw [mul_comm]
  exact mul_inv_of_norm_ne_zero a hnorm

def ofWire (a : EvmSemantics.Crypto.Bls12381.Fp12) : Carrier :=
  { c0 := LawfulFp6.ofWire a.c0
    c1 := LawfulFp6.ofWire a.c1 }

def toWire (a : Carrier) : EvmSemantics.Crypto.Bls12381.Fp12 :=
  { c0 := LawfulFp6.toWire a.c0
    c1 := LawfulFp6.toWire a.c1 }

@[simp] theorem toWire_ofWire (a : EvmSemantics.Crypto.Bls12381.Fp12) :
    toWire (ofWire a) = a := by
  cases a
  simp [toWire, ofWire]

@[simp] theorem ofWire_toWire (a : Carrier) : ofWire (toWire a) = a := by
  cases a
  simp [toWire, ofWire]

end Challenge.Bls12381.ProofSupport.LawfulFp12
