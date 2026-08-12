import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDeltaBridge

set_option warningAsError true

/-! Opaque output and preserved-slope lookups after the delta block. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem pointAddUnequalDeltaEnv_eq (ctx : PointAddUnequalDeltaContext) :
    pointAddUnequalDeltaEnv ctx =
      VEnv.set
        (VEnv.set ctx.env "\x00138" (pointAddUnequalDeltaResult ctx).1)
        "\x00139" (pointAddUnequalDeltaResult ctx).2 := by
  rw [pointAddUnequalDeltaEnv, pointAddUnequalDeltaWorkEnv,
    pointAddUnequalDeltaHighOutEnv, pointAddUnequalDeltaSelectedEnv]
  rw [venv_set_append_of_names_ne _ _ _ _ (by simp)]
  rw [venv_set_append_of_names_ne _ _ _ _ (by simp)]
  apply restore_append_of_length_eq
  rw [venv_set_length, venv_set_length]

theorem pointAddUnequalDeltaConcreteEnv_hi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalDeltaConcreteEnv yst out left right) "\x00138" =
      some (pointAddUnequalDeltaResult
        (pointAddUnequalDeltaContext yst out left right)).1 := by
  rw [pointAddUnequalDeltaConcreteEnv, pointAddUnequalDeltaEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  apply venv_get_set_self_of_some
  rfl

theorem pointAddUnequalDeltaConcreteEnv_lo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalDeltaConcreteEnv yst out left right) "\x00139" =
      some (pointAddUnequalDeltaResult
        (pointAddUnequalDeltaContext yst out left right)).2 := by
  rw [pointAddUnequalDeltaConcreteEnv, pointAddUnequalDeltaEnv_eq]
  apply venv_get_set_self_of_some
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rfl

private theorem pointAddUnequalXSubEnv_lambdaHi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalXSubEnv yst out left right) "\x00134" =
      some (pointAddUnequalLambdaResult yst out left right).1 := by
  rw [pointAddUnequalXSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [pointAddUnequalXSubLeftEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rfl

private theorem pointAddUnequalXSubEnv_lambdaLo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalXSubEnv yst out left right) "\x00135" =
      some (pointAddUnequalLambdaResult yst out left right).2 := by
  rw [pointAddUnequalXSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [pointAddUnequalXSubLeftEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rfl

theorem pointAddUnequalDeltaConcreteEnv_lambdaHi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalDeltaConcreteEnv yst out left right) "\x00134" =
      some (pointAddUnequalLambdaResult yst out left right).1 := by
  rw [pointAddUnequalDeltaConcreteEnv, pointAddUnequalDeltaEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  change VEnv.get
    (pointAddUnequalDeltaInitialConcreteEnv yst out left right) "\x00134" = _
  rw [pointAddUnequalDeltaInitialConcreteEnv]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact pointAddUnequalXSubEnv_lambdaHi yst out left right

theorem pointAddUnequalDeltaConcreteEnv_lambdaLo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalDeltaConcreteEnv yst out left right) "\x00135" =
      some (pointAddUnequalLambdaResult yst out left right).2 := by
  rw [pointAddUnequalDeltaConcreteEnv, pointAddUnequalDeltaEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  change VEnv.get
    (pointAddUnequalDeltaInitialConcreteEnv yst out left right) "\x00135" = _
  rw [pointAddUnequalDeltaInitialConcreteEnv]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact pointAddUnequalXSubEnv_lambdaLo yst out left right

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
