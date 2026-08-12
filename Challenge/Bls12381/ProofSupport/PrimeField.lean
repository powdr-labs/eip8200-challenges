import Challenge.EvmProof.ModPow
import EvmSemantics.Crypto.Bls12381.Curve
import Mathlib.Data.List.Prime
import Mathlib.NumberTheory.LucasPrimality

set_option warningAsError true

/-!
# Kernel-checked BLS12-381 prime-field boundary

The pinned semantics represents field elements as `Fin p`, but its custom
inverse is implemented by an opaque partial function and exposes no equation
or correctness theorem.  This module therefore uses the canonical
`Fin p ≃+* ZMod p` bridge for lawful algebra.  A separate fixed-modulus Lucas
certificate will discharge `p.Prime`; equivalence to the pinned opaque inverse
is deliberately not part of this boundary.
-/

namespace Challenge.Bls12381.ProofSupport.PrimeField

open EvmSemantics.Crypto.Bls12381
open EvmSemantics.EVM

/-- A shallow Lucas certificate node: callers provide the complete prime
factor list of `candidate - 1`, child primality proofs, and modular-power
evidence.  Large certificates can therefore be assembled bottom-up without
large primality decision procedures. -/
theorem prime_of_lucas_factors (candidate witness : Nat) (factors : List Nat)
    (hprod : factors.prod = candidate - 1)
    (hprime : ∀ factor ∈ factors, Nat.Prime factor)
    (hpow : (witness : ZMod candidate) ^ (candidate - 1) = 1)
    (horders : ∀ factor ∈ factors,
      (witness : ZMod candidate) ^ ((candidate - 1) / factor) ≠ 1) :
    Nat.Prime candidate := by
  apply lucas_primality candidate witness hpow
  intro q hq hdiv
  apply horders q
  apply mem_list_primes_of_dvd_prod (Nat.prime_iff.mp hq)
    (fun factor hfactor => Nat.prime_iff.mp (hprime factor hfactor))
  rw [hprod]
  exact hdiv

/-- Casting the terminating MODEXP evaluator into `ZMod` gives ordinary
monoid exponentiation. -/
theorem natCast_modPow_eq_pow (base exponent modulus : Nat) (hmodulus : 0 < modulus) :
    (Precompile.modPow base exponent modulus : ZMod modulus) =
      (base : ZMod modulus) ^ exponent := by
  rw [Challenge.EvmProof.ModPow.eval_eq, if_neg (Nat.ne_of_gt hmodulus)]
  simpa only [Nat.cast_pow] using ZMod.natCast_mod (base ^ exponent) modulus

/-- A shallow Lucas node whose modular evidence uses the terminating MODEXP
evaluator, keeping concrete proof reduction logarithmic in the exponent. -/
theorem prime_of_modPow_lucas_factors (candidate witness : Nat) (factors : List Nat)
    (hcandidate : 1 < candidate)
    (hprod : factors.prod = candidate - 1)
    (hprime : ∀ factor ∈ factors, Nat.Prime factor)
    (hpow : Precompile.modPow witness (candidate - 1) candidate = 1)
    (horders : ∀ factor ∈ factors,
      Precompile.modPow witness ((candidate - 1) / factor) candidate ≠ 1) :
    Nat.Prime candidate := by
  apply prime_of_lucas_factors candidate witness factors hprod hprime
  · calc
      (witness : ZMod candidate) ^ (candidate - 1) =
          (Precompile.modPow witness (candidate - 1) candidate : Nat) :=
        (natCast_modPow_eq_pow witness (candidate - 1) candidate
          (Nat.zero_lt_of_lt hcandidate)).symm
      _ = 1 := by rw [hpow]; norm_num
  · intro factor hfactor heq
    apply horders factor hfactor
    apply Nat.ModEq.eq_of_lt_of_lt
    · rw [← ZMod.natCast_eq_natCast_iff]
      rw [natCast_modPow_eq_pow witness ((candidate - 1) / factor) candidate
        (Nat.zero_lt_of_lt hcandidate)]
      simpa using heq
    · exact Challenge.EvmProof.ModPow.eval_lt
        (Nat.zero_lt_of_lt hcandidate)
    · exact hcandidate

abbrev LawfulFp := ZMod p

/-- Canonical ring equivalence between the wire-level `Fin p` carrier and the
lawful local algebraic carrier.  It is available before primality is known;
field/inverse facts additionally consume the fixed prime certificate. -/
def finEquiv : Fp ≃+* LawfulFp := ZMod.finEquiv p

@[simp] theorem finEquiv_apply_val (a : Fp) :
    (finEquiv a).val = a.val := rfl

theorem lawful_mul_inv_cancel (hp : Nat.Prime p) (a : LawfulFp) (ha : a ≠ 0) :
    a * a⁻¹ = 1 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  simpa [mul_comm] using inv_mul_cancel₀ ha

end Challenge.Bls12381.ProofSupport.PrimeField
