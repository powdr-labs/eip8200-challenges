import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubLeftEnvEq

set_option warningAsError true

/-! Opaque lookup boundary for the restored first-subtraction environment. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem pointAddDoubleXSubLeftEnv_hi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleXSubLeftEnv yst out left right) "\x00122" =
      some (pointAddDoubleXSubLeftResult yst out left right).1 := by
  rw [pointAddDoubleXSubLeftEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  apply venv_get_set_self_of_some
  rfl

theorem pointAddDoubleXSubLeftEnv_lo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleXSubLeftEnv yst out left right) "\x00123" =
      some (pointAddDoubleXSubLeftResult yst out left right).2 := by
  rw [pointAddDoubleXSubLeftEnv_eq]
  apply venv_get_set_self_of_some
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
