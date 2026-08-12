import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleDeltaBridge

set_option warningAsError true

/-! Opaque output and preserved-slope lookups after the delta block. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem pointAddDoubleDeltaEnv_eq (ctx : PointAddDoubleDeltaContext) :
    pointAddDoubleDeltaEnv ctx =
      VEnv.set
        (VEnv.set ctx.env "\x00124" (pointAddDoubleDeltaResult ctx).1)
        "\x00125" (pointAddDoubleDeltaResult ctx).2 := by
  rw [pointAddDoubleDeltaEnv, pointAddDoubleDeltaWorkEnv,
    pointAddDoubleDeltaHighOutEnv, pointAddDoubleDeltaSelectedEnv]
  rw [venv_set_append_of_names_ne _ _ _ _ (by simp)]
  rw [venv_set_append_of_names_ne _ _ _ _ (by simp)]
  apply restore_append_of_length_eq
  rw [venv_set_length, venv_set_length]

theorem pointAddDoubleDeltaConcreteEnv_hi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleDeltaConcreteEnv yst out left right) "\x00124" =
      some (pointAddDoubleDeltaResult
        (pointAddDoubleDeltaContext yst out left right)).1 := by
  rw [pointAddDoubleDeltaConcreteEnv, pointAddDoubleDeltaEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  apply venv_get_set_self_of_some
  rfl

theorem pointAddDoubleDeltaConcreteEnv_lo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleDeltaConcreteEnv yst out left right) "\x00125" =
      some (pointAddDoubleDeltaResult
        (pointAddDoubleDeltaContext yst out left right)).2 := by
  rw [pointAddDoubleDeltaConcreteEnv, pointAddDoubleDeltaEnv_eq]
  apply venv_get_set_self_of_some
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rfl

private theorem pointAddDoubleXSubEnv_lambdaHi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleXSubEnv yst out left right) "\x00120" =
      some (pointAddDoubleLambdaResult yst out left right).1 := by
  rw [pointAddDoubleXSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [pointAddDoubleXSubLeftEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rfl

private theorem pointAddDoubleXSubEnv_lambdaLo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleXSubEnv yst out left right) "\x00121" =
      some (pointAddDoubleLambdaResult yst out left right).2 := by
  rw [pointAddDoubleXSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [pointAddDoubleXSubLeftEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rfl

theorem pointAddDoubleDeltaConcreteEnv_lambdaHi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleDeltaConcreteEnv yst out left right) "\x00120" =
      some (pointAddDoubleLambdaResult yst out left right).1 := by
  rw [pointAddDoubleDeltaConcreteEnv, pointAddDoubleDeltaEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  change VEnv.get
    (pointAddDoubleDeltaInitialConcreteEnv yst out left right) "\x00120" = _
  rw [pointAddDoubleDeltaInitialConcreteEnv]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact pointAddDoubleXSubEnv_lambdaHi yst out left right

theorem pointAddDoubleDeltaConcreteEnv_lambdaLo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleDeltaConcreteEnv yst out left right) "\x00121" =
      some (pointAddDoubleLambdaResult yst out left right).2 := by
  rw [pointAddDoubleDeltaConcreteEnv, pointAddDoubleDeltaEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  change VEnv.get
    (pointAddDoubleDeltaInitialConcreteEnv yst out left right) "\x00121" = _
  rw [pointAddDoubleDeltaInitialConcreteEnv]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact pointAddDoubleXSubEnv_lambdaLo yst out left right

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
