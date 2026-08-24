import Challenge.EvmProof.ModPow

set_option warningAsError true

/-!
# Implementation-independent modular-exponentiation results

This file is the arithmetic seam shared by software MODEXP implementations.
It contains no Yul AST, function ABI, compiler artifact, or EVM precompile-call
semantics.  `Precompile.modPow` is used only as the pinned terminating natural-
number function defining modular exponentiation.
-/

namespace Challenge.YulProof.SoftwareModexpMath

open EvmSemantics.EVM

/-- A mathematical modular-exponentiation operation.  `outputSize` records the
fixed-width byte encoding required by an implementation ABI. -/
structure Operation where
  base : Nat
  exponent : Nat
  modulus : Nat
  outputSize : Nat
deriving DecidableEq, Repr

/-- The unique natural-number result of an operation. -/
def Operation.resultNat (operation : Operation) : Nat :=
  Precompile.modPow operation.base operation.exponent operation.modulus

/-- A natural number is the mathematical result of `operation`. -/
def ResultNat (operation : Operation) (output : Nat) : Prop :=
  output = operation.resultNat

/-- A byte list is the exact fixed-width big-endian result of `operation`. -/
def ResultBytes (operation : Operation) (output : List UInt8) : Prop :=
  output = (Precompile.natToBytes operation.resultNat operation.outputSize).toList

theorem resultNat_zero_modulus (base exponent outputSize : Nat) :
    ({ base, exponent, modulus := 0, outputSize } : Operation).resultNat = 0 := by
  simp [Operation.resultNat, Precompile.modPow]

theorem resultNat_lt_modulus {operation : Operation}
    (hmodulus : 0 < operation.modulus) :
    operation.resultNat < operation.modulus := by
  exact Challenge.EvmProof.ModPow.eval_lt hmodulus

theorem resultBytes (operation : Operation) :
    ResultBytes operation
      (Precompile.natToBytes operation.resultNat operation.outputSize).toList := by
  rfl

end Challenge.YulProof.SoftwareModexpMath
