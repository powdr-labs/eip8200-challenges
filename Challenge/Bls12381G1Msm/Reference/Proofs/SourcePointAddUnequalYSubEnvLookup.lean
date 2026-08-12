import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalYSubBridge
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDeltaEnvLookup

set_option warningAsError true

/-! Opaque result and preserved-coordinate lookups after the final y subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem pointAddUnequalYSubEnv_eq (ctx : PointAddUnequalYSubContext) :
    pointAddUnequalYSubEnv ctx =
      VEnv.set
        (VEnv.set ctx.env "\x00140" (pointAddUnequalYSubResult ctx).1)
        "\x00141" (pointAddUnequalYSubResult ctx).2 := by
  rw [pointAddUnequalYSubEnv, pointAddUnequalYSubWorkEnv,
    pointAddUnequalYSubHighOutEnv, pointAddUnequalYSubSelectedEnv]
  rw [venv_set_append_of_names_ne _ _ _ _ (by simp)]
  rw [venv_set_append_of_names_ne _ _ _ _ (by simp)]
  apply restore_append_of_length_eq
  rw [venv_set_length, venv_set_length]

theorem pointAddUnequalYMulEnv_xHi (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddUnequalYMulEnv yst out left right) "\x00136" =
      some (pointAddUnequalXSubResult yst out left right).1 := by
  rw [pointAddUnequalYMulEnv]
  simp only [List.zip, List.zipWith, List.cons_append, List.nil_append]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [pointAddUnequalDeltaConcreteEnv, pointAddUnequalDeltaEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  change VEnv.get (pointAddUnequalDeltaInitialConcreteEnv yst out left right)
    "\x00136" = _
  rw [pointAddUnequalDeltaInitialConcreteEnv]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact pointAddUnequalXSubEnv_hi yst out left right

theorem pointAddUnequalYMulEnv_xLo (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddUnequalYMulEnv yst out left right) "\x00137" =
      some (pointAddUnequalXSubResult yst out left right).2 := by
  rw [pointAddUnequalYMulEnv]
  simp only [List.zip, List.zipWith, List.cons_append, List.nil_append]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [pointAddUnequalDeltaConcreteEnv, pointAddUnequalDeltaEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  change VEnv.get (pointAddUnequalDeltaInitialConcreteEnv yst out left right)
    "\x00137" = _
  rw [pointAddUnequalDeltaInitialConcreteEnv]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact pointAddUnequalXSubEnv_lo yst out left right

theorem pointAddUnequalYMulEnv_tempHi (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddUnequalYMulEnv yst out left right) "\x00138" =
      some (pointAddUnequalDeltaResult
        (pointAddUnequalDeltaContext yst out left right)).1 := by
  rw [pointAddUnequalYMulEnv]
  simp only [List.zip, List.zipWith, List.cons_append, List.nil_append]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  exact pointAddUnequalDeltaConcreteEnv_hi yst out left right

theorem pointAddUnequalYMulEnv_tempLo (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddUnequalYMulEnv yst out left right) "\x00139" =
      some (pointAddUnequalDeltaResult
        (pointAddUnequalDeltaContext yst out left right)).2 := by
  rw [pointAddUnequalYMulEnv]
  simp only [List.zip, List.zipWith, List.cons_append, List.nil_append]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  exact pointAddUnequalDeltaConcreteEnv_lo yst out left right

theorem pointAddUnequalYSubConcreteEnv_xHi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalYSubConcreteEnv yst out left right) "\x00136" =
      some (pointAddUnequalXSubResult yst out left right).1 := by
  rw [pointAddUnequalYSubConcreteEnv, pointAddUnequalYSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  change VEnv.get (pointAddUnequalYMulEnv yst out left right) "\x00136" = _
  exact pointAddUnequalYMulEnv_xHi yst out left right

theorem pointAddUnequalYSubConcreteEnv_xLo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalYSubConcreteEnv yst out left right) "\x00137" =
      some (pointAddUnequalXSubResult yst out left right).2 := by
  rw [pointAddUnequalYSubConcreteEnv, pointAddUnequalYSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  change VEnv.get (pointAddUnequalYMulEnv yst out left right) "\x00137" = _
  exact pointAddUnequalYMulEnv_xLo yst out left right

theorem pointAddUnequalYSubConcreteEnv_yHi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalYSubConcreteEnv yst out left right) "\x00140" =
      some (pointAddUnequalYSubResult
        (pointAddUnequalYSubContext yst out left right)).1 := by
  rw [pointAddUnequalYSubConcreteEnv, pointAddUnequalYSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  apply venv_get_set_self_of_some
  rfl

theorem pointAddUnequalYSubConcreteEnv_yLo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalYSubConcreteEnv yst out left right) "\x00141" =
      some (pointAddUnequalYSubResult
        (pointAddUnequalYSubContext yst out left right)).2 := by
  rw [pointAddUnequalYSubConcreteEnv, pointAddUnequalYSubEnv_eq]
  apply venv_get_set_self_of_some
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rfl

theorem pointAddUnequalYSubConcreteEnv_tempHi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalYSubConcreteEnv yst out left right) "\x00138" =
      some (pointAddUnequalDeltaResult
        (pointAddUnequalDeltaContext yst out left right)).1 := by
  rw [pointAddUnequalYSubConcreteEnv, pointAddUnequalYSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  change VEnv.get (pointAddUnequalYMulEnv yst out left right) "\x00138" = _
  exact pointAddUnequalYMulEnv_tempHi yst out left right

theorem pointAddUnequalYSubConcreteEnv_tempLo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalYSubConcreteEnv yst out left right) "\x00139" =
      some (pointAddUnequalDeltaResult
        (pointAddUnequalDeltaContext yst out left right)).2 := by
  rw [pointAddUnequalYSubConcreteEnv, pointAddUnequalYSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  change VEnv.get (pointAddUnequalYMulEnv yst out left right) "\x00139" = _
  exact pointAddUnequalYMulEnv_tempLo yst out left right

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
