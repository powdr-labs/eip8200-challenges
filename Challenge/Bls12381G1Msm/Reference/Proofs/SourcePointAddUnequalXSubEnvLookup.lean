import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubEnvEq

set_option warningAsError true

/-! Opaque `x3` lookups after both unequal-point x subtractions. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem pointAddUnequalXSubEnv_hi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalXSubEnv yst out left right) "\x00136" =
      some (pointAddUnequalXSubResult yst out left right).1 := by
  rw [pointAddUnequalXSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  apply venv_get_set_self_of_some
  exact pointAddUnequalXSubLeftEnv_hi yst out left right

theorem pointAddUnequalXSubEnv_lo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalXSubEnv yst out left right) "\x00137" =
      some (pointAddUnequalXSubResult yst out left right).2 := by
  rw [pointAddUnequalXSubEnv_eq]
  apply venv_get_set_self_of_some
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  exact pointAddUnequalXSubLeftEnv_lo yst out left right

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
