import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubLeftEnvEq

set_option warningAsError true

/-! Opaque lookup boundary for the restored first-subtraction environment. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem pointAddUnequalXSubLeftEnv_hi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalXSubLeftEnv yst out left right) "\x00136" =
      some (pointAddUnequalXSubLeftResult yst out left right).1 := by
  rw [pointAddUnequalXSubLeftEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  apply venv_get_set_self_of_some
  rfl

theorem pointAddUnequalXSubLeftEnv_lo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalXSubLeftEnv yst out left right) "\x00137" =
      some (pointAddUnequalXSubLeftResult yst out left right).2 := by
  rw [pointAddUnequalXSubLeftEnv_eq]
  apply venv_get_set_self_of_some
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
