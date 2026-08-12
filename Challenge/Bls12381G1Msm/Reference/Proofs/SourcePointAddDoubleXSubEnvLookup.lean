import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubEnvEq

set_option warningAsError true

/-! Opaque `x3` lookups after both point-double x subtractions. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem pointAddDoubleXSubEnv_hi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleXSubEnv yst out left right) "\x00122" =
      some (pointAddDoubleXSubResult yst out left right).1 := by
  rw [pointAddDoubleXSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  apply venv_get_set_self_of_some
  exact pointAddDoubleXSubLeftEnv_hi yst out left right

theorem pointAddDoubleXSubEnv_lo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleXSubEnv yst out left right) "\x00123" =
      some (pointAddDoubleXSubResult yst out left right).2 := by
  rw [pointAddDoubleXSubEnv_eq]
  apply venv_get_set_self_of_some
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  exact pointAddDoubleXSubLeftEnv_lo yst out left right

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
