import Challenge.Bls12381.ProofSupport.PrimeField

set_option warningAsError true

/-!
# Kernel-checked BLS12-381 primality certificate

The certificate is assembled bottom-up from shallow Lucas nodes.  Concrete
modular powers are checked by the terminating square-and-multiply evaluator,
one recursion equation at a time; this avoids expanding a linear `Monoid.pow`
term or trusting a native evaluator.
-/

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate

open EvmSemantics.EVM
open PrimeField

/-- Reduce one concrete fast modular-power computation in logarithmically
many kernel-checked steps. -/
macro "bls_norm_mod_pow" : tactic =>
  `(tactic|
    (unfold Precompile.modPow
     norm_num
     repeat
       rw [Precompile.modPowAux]
       norm_num))

theorem prime281 : Nat.Prime 281 := by decide +kernel
theorem prime137 : Nat.Prime 137 := by decide +kernel
theorem prime947 : Nat.Prime 947 := by decide +kernel
theorem prime67 : Nat.Prime 67 := by decide +kernel
theorem prime4349 : Nat.Prime 4349 := by decide +kernel
theorem prime5 : Nat.Prime 5 := by decide +kernel
theorem prime11 : Nat.Prime 11 := by decide +kernel
theorem prime13 : Nat.Prime 13 := by decide +kernel
theorem prime17 : Nat.Prime 17 := by decide +kernel
theorem prime23 : Nat.Prime 23 := by decide +kernel
theorem prime7 : Nat.Prime 7 := by decide +kernel
theorem prime41 : Nat.Prime 41 := by decide +kernel
theorem prime43 : Nat.Prime 43 := by decide +kernel
theorem prime53 : Nat.Prime 53 := by decide +kernel
theorem prime97 : Nat.Prime 97 := by decide +kernel
theorem prime151 : Nat.Prime 151 := by decide +kernel
theorem prime191 : Nat.Prime 191 := by decide +kernel
theorem prime409 : Nat.Prime 409 := by decide +kernel
theorem prime449 : Nat.Prime 449 := by decide +kernel
theorem prime19 : Nat.Prime 19 := by decide +kernel
theorem prime31 : Nat.Prime 31 := by decide +kernel
theorem prime89 : Nat.Prime 89 := by decide +kernel
theorem prime113 : Nat.Prime 113 := by decide +kernel
theorem prime467 : Nat.Prime 467 := by decide +kernel
theorem prime941 : Nat.Prime 941 := by decide +kernel

end Challenge.Bls12381.ProofSupport.PrimeCertificate

