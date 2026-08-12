import Challenge.Bls12381.ProofSupport.PrimeCertificate
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

set_option warningAsError true

/-!
# Lawful BLS12-381 quadratic extension

The pinned wire semantics stores `Fp2` as two `Fin p` components but routes
inversion through an opaque partial implementation.  This module instead
builds the same `u² = -1` arithmetic over the certified field `ZMod p` and
keeps explicit, inverse-free adapters to and from the wire carrier.
-/

namespace Challenge.Bls12381.ProofSupport.LawfulFp2

open EvmSemantics.Crypto.Bls12381

abbrev Base := PrimeField.LawfulFp

theorem p_mod_four : p % 4 = 3 := by
  norm_num [p, absU]

instance nonsquarePolynomial :
    Fact (∀ r : Base, r ^ 2 ≠ (-1 : Base) + 0 * r) := ⟨by
  intro r hr
  have hsquare : r ^ 2 = (-1 : Base) := by simpa using hr
  exact (ZMod.mod_four_ne_three_of_sq_eq_neg_one hsquare) p_mod_four⟩

/-- The lawful `Fp2` carrier, with generator satisfying `u² = -1`. -/
abbrev Carrier := QuadraticAlgebra Base (-1) 0

/-- Inverse-free adapter from the pinned two-`Fin p` wire carrier. -/
def ofWire (a : EvmSemantics.Crypto.Bls12381.Fp2) : Carrier :=
  ⟨PrimeField.finEquiv a.c0, PrimeField.finEquiv a.c1⟩

/-- Inverse-free adapter back to the pinned wire carrier. -/
def toWire (a : Carrier) : EvmSemantics.Crypto.Bls12381.Fp2 :=
  { c0 := PrimeField.finEquiv.symm a.re
    c1 := PrimeField.finEquiv.symm a.im }

@[simp] theorem toWire_ofWire (a : EvmSemantics.Crypto.Bls12381.Fp2) :
    toWire (ofWire a) = a := by
  cases a
  simp [toWire, ofWire]

@[simp] theorem ofWire_toWire (a : Carrier) : ofWire (toWire a) = a := by
  cases a
  simp [toWire, ofWire]

theorem ofWire_injective : Function.Injective ofWire :=
  Function.LeftInverse.injective toWire_ofWire

@[simp] theorem ofWire_add (a b : EvmSemantics.Crypto.Bls12381.Fp2) :
    ofWire (a + b) = ofWire a + ofWire b := by
  change ofWire (_root_.Fp2.add a b) = _
  cases a
  cases b
  apply QuadraticAlgebra.ext <;> simp [ofWire, _root_.Fp2.add]

@[simp] theorem ofWire_mul (a b : EvmSemantics.Crypto.Bls12381.Fp2) :
    ofWire (a * b) = ofWire a * ofWire b := by
  change ofWire (_root_.Fp2.mul a b) = _
  cases a
  cases b
  apply QuadraticAlgebra.ext <;> simp [ofWire, _root_.Fp2.mul] <;> ring

@[simp] theorem ofWire_square (a : EvmSemantics.Crypto.Bls12381.Fp2) :
    ofWire (a ^ 2) = ofWire a ^ 2 := by
  change ofWire (_root_.Fp2.square a) = _
  cases a
  apply QuadraticAlgebra.ext <;>
    simp [ofWire, _root_.Fp2.square, pow_two] <;> ring

theorem mul_inv_cancel (a : Carrier) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  simpa [mul_comm] using inv_mul_cancel₀ ha

end Challenge.Bls12381.ProofSupport.LawfulFp2
