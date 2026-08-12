import EvmSemantics.EVM.Precompile
import Mathlib.Tactic.Ring

set_option warningAsError true

/-!
# Executable modular exponentiation

Generic correctness facts for the terminating square-and-multiply evaluator
used by the MODEXP precompile.  These belong in the EVM proof layer because
fixed-field primality certificates also need a logarithmic kernel evaluator.
-/

namespace Challenge.EvmProof.ModPow

open EvmSemantics.EVM

theorem aux_mod (base acc modulus exponent : Nat) :
    Precompile.modPowAux base acc modulus exponent % modulus =
      (acc * base ^ exponent) % modulus := by
  induction exponent using Nat.strong_induction_on generalizing base acc with
  | _ exponent ih =>
    unfold Precompile.modPowAux
    split
    · next h => subst h; simp
    · next h =>
      have hlt : exponent / 2 < exponent :=
        Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
      rw [ih (exponent / 2) hlt]
      have hpow : base ^ exponent =
          (base * base) ^ (exponent / 2) * base ^ (exponent % 2) := by
        rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_add]
        congr 1
        omega
      rw [hpow]
      rcases Nat.mod_two_eq_zero_or_one exponent with hpar | hpar
      · rw [if_neg (by omega), hpar, Nat.pow_zero, Nat.mul_one,
          Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod]
      · rw [if_pos hpar, hpar, Nat.pow_one,
          Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod]
        rw [Nat.mul_assoc, Nat.mul_comm base ((base * base) ^ (exponent / 2))]

theorem aux_lt {base acc modulus exponent : Nat} (hmodulus : 0 < modulus)
    (hacc : acc < modulus) :
    Precompile.modPowAux base acc modulus exponent < modulus := by
  induction exponent using Nat.strong_induction_on generalizing base acc with
  | _ exponent ih =>
    unfold Precompile.modPowAux
    split
    · exact hacc
    · next h =>
      apply ih (exponent / 2)
        (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide))
      split
      · exact Nat.mod_lt _ hmodulus
      · exact hacc

theorem eval_eq (base exponent modulus : Nat) :
    Precompile.modPow base exponent modulus =
      if modulus = 0 then 0 else base ^ exponent % modulus := by
  unfold Precompile.modPow
  split
  · rfl
  · next hm0 =>
    split
    · next hm1 =>
      subst modulus
      exact (Nat.mod_one _).symm
    · next hm1 =>
      have hmpos : 0 < modulus := Nat.pos_of_ne_zero hm0
      have hone : 1 < modulus := by omega
      have hlt := aux_lt (base := base % modulus) (exponent := exponent)
        hmpos hone
      calc
        Precompile.modPowAux (base % modulus) 1 modulus exponent =
            Precompile.modPowAux (base % modulus) 1 modulus exponent % modulus :=
          (Nat.mod_eq_of_lt hlt).symm
        _ = (1 * (base % modulus) ^ exponent) % modulus := aux_mod _ _ _ _
        _ = (base % modulus) ^ exponent % modulus := by rw [Nat.one_mul]
        _ = base ^ exponent % modulus := (Nat.pow_mod _ _ _).symm

theorem eval_lt {base exponent modulus : Nat} (hmodulus : 0 < modulus) :
    Precompile.modPow base exponent modulus < modulus := by
  rw [eval_eq, if_neg (Nat.ne_of_gt hmodulus)]
  exact Nat.mod_lt _ hmodulus

end Challenge.EvmProof.ModPow
